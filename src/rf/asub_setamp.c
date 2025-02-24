#include <errno.h>
#include <string.h>
#include <errlog.h>
#include <recGbl.h>
#include <alarm.h>
#include <menuFtype.h>

#include <epicsTypes.h>

#include <subRecord.h>
#include <aSubRecord.h>

#include <registryFunction.h>
#include <epicsExport.h>

#include <epicsMath.h>

#define PI 3.14159265359

#define MIN(A,B) ((A)<(B) ? (A) : (B))
#define MAX(A,B) ((A)>(B) ? (A) : (B))

/* Subroutine to set cavity amplitude (RFS) */
#define MODE_SELAP   0
#define MODE_SELA    1
#define MODE_SEL     2
#define MODE_SEL_RAW 3
#define MODE_PULSE   4
#define MODE_CHIRP   5

static
void setamp_calc_ssa(double max_magn, double max_imag, double adesv, double imped, double freq, 
double *pol_x, double *pol_y, double *sqrtu, double qloaded, double fwd_fs, double *ssa, double *ssan)
{
    /* Policy maximum X/Y */
    *pol_x = max_magn * sqrt(1 - max_imag);
    *pol_y = max_magn * sqrt(max_imag);

    /* Cavity sqrt(energy) 
     * V/(sqrt( (shunt impedance) * 2pi * (cav freq)))
     */
    *sqrtu = adesv / (sqrt(imped * 2 * PI * freq));

    /* Target SSA ADC normalized amplitude */
    *ssa = *sqrtu * sqrt((PI * freq) / (2 * qloaded));
    *ssan = *ssa / fwd_fs;
}

static 
void setamp_calc_x_fb(double ssa_slope, double ssa_minx, double ssa_ped, double *ssan, 
double *lowslope, double *x_lo, double *x_hi)
{
	*x_lo = ssa_slope * *ssan * 0.83;
	*x_hi = (ssa_slope * *ssan + ssa_ped) * 1.15;
	*x_hi = MIN(*x_hi, *lowslope * *ssan * 1.15);
}

static
void setamp_calc_x(double ssa_slope, double *ssan, double *lowslope, double *x_lo)
{
	*x_lo = ssa_slope * *ssan;
	*x_lo = MIN(*x_lo, *lowslope * *ssan);
}

static 
void setamp_calc(short debug, short amp_close, double max_magn, double max_imag, double adesv, double imped, double freq, 
double *pol_x, double *pol_y, double *sqrtu, double qloaded, double fwd_fs, double ssa_slope, double ssa_minx, 
double ssa_ped, double *ssa, double *ssan, double *lowslope, double *x_lo, double *x_hi)
{

    setamp_calc_ssa(max_magn, max_imag, adesv, imped, freq, pol_x, pol_y, sqrtu, qloaded, fwd_fs, ssa, ssan);

    /* Calculate values for X limit registers */

    *lowslope = (ssa_slope * ssa_minx + ssa_ped) / ssa_minx;

    if (debug) {
        printf("setAmpl: max_magn %f max_imag %f calc policy x %f y %f\n", max_magn, max_imag, *pol_x, *pol_y);
        printf("setAmpl: to affine sqrtu %f sqrt(J) ssa %f ssan %f\n", *sqrtu, *ssa, *ssan);
    }

    if (amp_close) { 
        setamp_calc_x_fb(ssa_slope, ssa_minx, ssa_ped, ssan, lowslope, x_lo, x_hi);
    }
    else {
        setamp_calc_x(ssa_slope, ssan, lowslope, x_lo);
        *x_hi = *x_lo;
    }
}

static 
long asub_setamp(aSubRecord *prec)
{
    double CORDIC_SCALE = 0.774483*pow(2,17);

    /* Inputs  */
    double ades   = *(double *)prec->a,
	imped     = *(double *)prec->b,
	freq      = *(double *)prec->c,
	qloaded   = *(double *)prec->d,
	fwd_fs    = *(double *)prec->e,
	cav_fs    = *(double *)prec->f,
	ssa_slope = *(double *)prec->i,
	ssa_minx  = *(double *)prec->j,
	ssa_ped   = *(double *)prec->k,
	max_magn  = *(double *)prec->l,
	max_imag  = *(double *)prec->m,
	sel_aset  = *(double *)prec->p,
	fudge     = *(double *)prec->q;

    short amp_close = *(short *)prec->g,
	pha_close   = *(short *)prec->h,
	rfctrl      = *(short *)prec->n,
	rfmodectrl  = *(short *)prec->o,
	rfmodeprev  = *(short *)prec->r;
 
    /* Intermediate results */
    double *sqrtu = (double *)prec->vala,
	*ssa      = (double *)prec->valb, /* SSA target */
	*ssan     = (double *)prec->valc, /* Normalized SSA target */
	*adcn     = (double *)prec->vald, /* Normalized cavity ADC */
	*pol_x    = (double *)prec->valf,
	*pol_y    = (double *)prec->valg,
	*lowslope = (double *)prec->valh,
	*x_lo     = (double *)prec->valm,
	*x_hi     = (double *)prec->valn;

    double y_lo, y_hi, x_lo_final, x_hi_final;

    epicsInt32 sel_lim, sel_lim_max;

    /* Outputs */
    epicsInt32 *setm = (epicsInt32 *)prec->vale,
        *lim_x_lo    = (epicsInt32 *)prec->valk,
        *lim_x_hi    = (epicsInt32 *)prec->vall,
        *lim_y_lo    = (epicsInt32 *)prec->valo,
        *lim_y_hi    = (epicsInt32 *)prec->valp;
    short *too_high  = (short *)prec->valq,
        *error_msg   = (short *)prec->valt,
        *rfmodecurr= (short *)prec->valu,
        *chirp     = (short *)prec->vali; /* chirp enable/disable */
    char  *msg     = (char *)prec->vals;

    *rfmodecurr = rfmodectrl;

    unsigned short *mask = (unsigned short *)prec->valr;

    *chirp = 0;

    short debug = (prec->tpro > 1) ? 1 : 0;

    /* Apply correction for measured beam energy gain */
    ades = ades / fudge;
    double adesv  = ades*1e6;

    unsigned short MASK_LIMS  = 0x1F;
    unsigned short MASK_CHIRP_SETUP = 0x40;
    unsigned short MASK_CHIRP_ENABLE = 0x80;
    unsigned short MASK_ERR = 0;

    *mask = MASK_ERR; /* Initialize to do not write registers */
    *error_msg = *too_high = 0; /* Initialize to no errors */

/* If RF control is set off, do not push values.
 * Leave error_msg at 0, though, because this is not 
 * considered an error state and no accompanying
 * message should be necessary
 */

    if (debug) {
        printf("%s: input values rfctrl %i rfmodectrl %i  prev %i ades %f MV imped %f ohms freq %f Hz qloaded %f "
               "amp_close %i pha_close %i ssa_slope %f ssa_minx %f ssa_ped %f "
               "fwd_fs %f sqrt(Watts) cav_fs %f MV mag_magn %f max_imag %f sel_aset %f fudge %f\n",
               prec->name, rfctrl, rfmodectrl, rfmodeprev, ades, imped, freq, qloaded, amp_close, pha_close, ssa_slope, 
               ssa_minx, ssa_ped, fwd_fs, cav_fs, max_magn, max_imag, sel_aset, fudge);
    }

	/* Chirp control. 
	 * If entering mode, set up chirp parameters
	 * If exiting mode, disable chirp
	 * If request is on/chirp, enable chirp
	 */
	if (rfmodectrl==MODE_CHIRP) {
		if (rfmodeprev != rfmodectrl) {
			*mask |= MASK_CHIRP_SETUP;
		}
		if (rfctrl != 0) {
			*chirp = 1;
			*mask |= MASK_CHIRP_ENABLE;
		}
	} else if (rfmodeprev == MODE_CHIRP) {
		*mask |= MASK_CHIRP_ENABLE;
	}

	if ( debug ) {
		printf("%s: after chirp, before pulse mask 0x%x\n",
			prec->name, *mask);
	}

	/* Pulse control. 
	 * If entering mode, set lim/mag registers to 0 and disable chirp 
	 */
	if (rfmodectrl == MODE_PULSE) {
		if (rfmodeprev != rfmodectrl) {
			*lim_x_lo = *lim_x_hi = *lim_y_lo = *lim_y_hi = *setm = 0;
			*mask |= MASK_LIMS | MASK_CHIRP_ENABLE;
		}
		return 0;
	}

	/* SEL raw amplitude control */
	if (rfmodectrl==MODE_SEL_RAW) {
		sel_lim_max = (epicsInt32)(79500 * max_magn); /* 79500 max value of lims registers */ 
		sel_lim = (epicsInt32)(floor((sel_aset/100)*79500));
		if ( sel_lim >= sel_lim_max ) {
			*lim_x_lo = *lim_x_hi = sel_lim_max;
		} else {
			*lim_x_lo = *lim_x_hi = sel_lim;
		}
		*lim_y_lo = *lim_y_hi = *setm = 0;
		if ( debug ) {
			printf("setAmpl: SEL raw mode: max lim %i sel_lim %i limxlo %i limxyhi %i limylo %i limyhi %i\n",
				sel_lim_max, sel_lim, *lim_x_lo, *lim_x_hi, *lim_y_lo, *lim_y_hi);
		}
	  
		if (rfctrl == 0) {
			return 0;
		}
		*mask |= MASK_LIMS;
		return 0;
	}

	setamp_calc(debug, amp_close, max_magn, max_imag, adesv, imped, freq, 
		pol_x, pol_y, sqrtu, qloaded, fwd_fs, ssa_slope, ssa_minx, 
		ssa_ped, ssa, ssan, lowslope, x_lo, x_hi);

    *too_high = (*x_hi > *pol_x) ? 1 : 0;
    x_lo_final = MIN(*x_lo, *pol_x); 
    x_hi_final = MIN(*x_hi, *pol_x); 

    *lim_x_lo = (epicsInt32)(79500 * (x_lo_final));
    *lim_x_hi = (epicsInt32)(79500 * (x_hi_final));

    /* Calculate value for set-magnitude register
     * Fudge already included in ades and cav_fs
     */
    *adcn = fudge * ades / cav_fs;
    *setm = (epicsInt32)(round(*adcn * CORDIC_SCALE));

    if (debug) {
        printf("setAmpl: to setmp adcn %f setm %i\n", *adcn, *setm);
    }

    /* Calculate values for Y limit registers */
    y_lo = y_hi = 0;
    if ( pha_close && (ades>0.0) ) {
        y_lo = - *pol_y;
        y_hi = *pol_y;
    }
    *lim_y_lo = (epicsInt32)(79500 * (y_lo));
    *lim_y_hi = (epicsInt32)(79500 * (y_hi));

    if (rfctrl == 0) {
        return 0;
    }

    /* Determine if settings should actually be written to registers.
     * TODO: Revisit numbers used in cav/fwd scale checks
     */
    if (*too_high) {
		/* current cavity frequency options are 1.3 and 3.9 GHz */
		if ((freq < 2.0e9) && (cav_fs < 25)) {
			sprintf(msg, "Overrange. Check cav scale");
		}
		else if (cav_fs < 5) {
			sprintf(msg, "Overrange. Check cav scale");
		}
		else if (fwd_fs < 50) {
			sprintf(msg, "Overrange. Check fwd scale");
		}
		else {
			sprintf(msg, "Overrange");
		}
		*error_msg = 1;
		return 0;
    }
    else if (isnan(*lowslope) || isinf(*lowslope)) {
        sprintf(msg, "Bad lowslope. Check SSA parms");
        *error_msg = 1;
        return 0;
    }

    *mask |= MASK_LIMS;
    return 0;
}

static void
ssa_ades_lim_calc(double pol_x, double ssa_ped, double ssa_slope,
double fwd_fs, double freq, double qloaded, double imped, double lowslope,
double *ssa_ades_lim_sela, double *ssa_ades_lim_sel, int debug, char *name)
{
	double ssan[4], ades[4], ssa, sqrtu;
	int i;

	ssan[0] = ((pol_x/1.15) - ssa_ped)/ssa_slope;
	ssan[1] = pol_x/lowslope/1.15;
	ssan[2] = pol_x/ssa_slope;
	ssan[3] = pol_x/lowslope;

	for (i = 0; i < 4; i++ ) {
		ssa = ssan[i] * fwd_fs;
		sqrtu =  ssa / sqrt((PI*freq)/(2*qloaded));
		ades[i] = (sqrtu * (sqrt(imped * 2 * PI * freq)))/1e6;
	}

	*ssa_ades_lim_sela = MAX( ades[0], ades[1] );

	*ssa_ades_lim_sel = MAX( ades[2], ades[3] );

	if (debug) {
		printf("%s ssa_ades_lim_calc:\n", name);
		printf("    SELA(P) %f %f, SEL %f %f\n", ades[0], ades[1], ades[2], ades[3]);
	}
}

static long
asub_setamp_diag(aSubRecord *prec)
{
	/* Inputs  */
	double ades   = *(double *)prec->a,
		imped     = *(double *)prec->b,
		freq      = *(double *)prec->c,
		qloaded   = *(double *)prec->d,
		fwd_fs    = *(double *)prec->e,
		ssa_slope = *(double *)prec->i,
		ssa_minx  = *(double *)prec->j,
		ssa_ped   = *(double *)prec->k,
		max_magn  = *(double *)prec->l,
		max_imag  = *(double *)prec->m;
 
	double ssa, ssan, lowslope, pol_x, pol_y, sqrtu;
	double x_lo, x_hi;
	int i;

	/* Outputs */
			/* 2 element arrays */
	double *pol_x_lo = (double *)prec->vala,      /* Policy x low limit */
		*pol_x_hi = (double *)prec->valb,      /* Policy x high limit */
		*pol_y_lo = (double *)prec->valc,      /* Policy y low limit */
		*pol_y_hi = (double *)prec->vald,      /* Policy y high limit */
		*pol_x_range = (double *)prec->vale,   /* Policy x low and high limits */
		*pol_y_range = (double *)prec->valf,   /* Policy y low and high limits */
		*sela_x_lo = (double *)prec->valg,     /* SELA(P) x low limit */
		*sela_x_hi = (double *)prec->valh,     /* SELA(P) x high limit */
		*sela_x_range  = (double *)prec->vali, /* SELA(P) x low and limits */
		*zeros = (double *)prec->valj,         /* Zero, two elements */
		*axis_x = (double *)prec->valk,        /* Graph x axis */
		*axis_y = (double *)prec->vall,        /* Graph y axis */
		*unit_x = (double *)prec->valm,        /* Unit semi-circle, x */                 
		*unit_y = (double *)prec->valn,        /* Unit semi-circle, y */              

		/* Scalars */
		*sel_x = (double *)prec->valo, /* SEL x */
		*ssa_ades_lim_sela = (double *)prec->valp, /* Max ADES in SELA/SELAP modes */
		*ssa_ades_lim_sel = (double *)prec->valq;  /* Max ADES in SEL mode */

	int debug = (prec->tpro > 1) ? 1 : 0;

	setamp_calc_ssa(max_magn, max_imag, ades*1e6, imped, freq, &pol_x, &pol_y, &sqrtu, qloaded, fwd_fs, &ssa, &ssan);
	lowslope = (ssa_slope * ssa_minx + ssa_ped) / ssa_minx;

	setamp_calc_x_fb(ssa_slope, ssa_minx, ssa_ped, &ssan, &lowslope, &x_lo, &x_hi);
	sela_x_range[0] = sela_x_lo[0] = sela_x_lo[1] = x_lo;
	sela_x_range[1] = sela_x_hi[0] = sela_x_hi[1] = x_hi;

	setamp_calc_x(ssa_slope, &ssan, &lowslope, &x_lo);
	*sel_x = x_lo;

	/* Add lowslope based options? */

	/* X and Y policy ranges */
	pol_x_lo[0] = pol_x_lo[1] = pol_x_range[0] = 0;
	pol_x_hi[0] = pol_x_hi[1] = pol_x_range[1] = pol_x;
	pol_y_lo[0] = pol_y_lo[1] = pol_y_range[0] = -pol_y;
	pol_y_hi[0] = pol_y_hi[1] = pol_y_range[1] = pol_y;

	zeros[0] = zeros[1] = 0;

	axis_x[0] = -2; 
	axis_x[1] = 2;
	axis_y[0] = -2; 
	axis_y[1] = 2;

	for (i = 0; i < 50; i++) {
		unit_x[i] = unit_x[100 - i - 1] = i * .02;
		unit_y[i] = sqrt(1 - pow(unit_x[i],2));
		unit_y[100 - i - 1] = -unit_y[i];
	}

	ssa_ades_lim_calc( pol_x, ssa_ped, ssa_slope, fwd_fs, freq, qloaded,
		imped, lowslope, ssa_ades_lim_sela, ssa_ades_lim_sel,
		debug, prec->name );

	return 0;
}

static
void asub_setampFEEDRegistrar(void)
{
    registryFunctionAdd("asub_setamp", (REGISTRYFUNCTION)&asub_setamp);
    registryFunctionAdd("asub_setamp_diag", (REGISTRYFUNCTION)&asub_setamp_diag);
}
epicsExportRegistrar(asub_setampFEEDRegistrar);
