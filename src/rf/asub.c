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

/* Fill in VALA with sequence
 *  [first, first+step, first+step*2, ...]
 *
 * result length is min(limit, .NOVA)
 *
record(asub, "$(N)") {
    field(SNAM, "asub_feed_timebase")
    field(FTA , "DOUBLE") # first value
    field(FTB , "DOUBLE") # step size
    field(FTC , "ULONG")  # max element count limit
    field(FTVA, "DOUBLE") # output array
    field(NOVA, "100")    # max output length
}
 */
static
long asub_feed_timebase(aSubRecord *prec)
{
    double val = *(double*)prec->a,
           step= *(double*)prec->b,
          *out = (double*)prec->vala;
    epicsUInt32 limit = *(epicsUInt32*)prec->c,
                i;

    if(limit > prec->nova)
        limit = prec->nova;
    if(prec->tpro>1)
        errlogPrintf("%s nova=%u\n", prec->name, (unsigned)prec->nova);
    if(prec->fta!=menuFtypeDOUBLE
        || prec->ftb!=menuFtypeDOUBLE
        || prec->ftc!=menuFtypeULONG
        || prec->ftva!=menuFtypeDOUBLE) {
        (void)recGblSetSevr(prec, CALC_ALARM, INVALID_ALARM);
        return EINVAL;
    }

    if(step==0.0)
        step = 1.0;

    if(prec->ftd==menuFtypeDOUBLE && prec->ned>=0) {
        double div = *(double*)prec->d;
        if(div!=0.0)
            step *= div;
    }

    for(i=0; i<limit; i++, val += step) {
        out[i] = val;
    }

    prec->neva = limit;
    return 0;
}

/* Count number of bits set
 *
record(sub, "$(N)") {
    field(SNAM, "sub_count_bits")
    field(A, "") # bit mask
}
 */
static
long sub_count_bits(subRecord *prec)
{
    epicsUInt32 mask = (epicsUInt32)prec->a;
    prec->val = 0;

    for(; mask; mask>>=1) {
        if(mask&1)
            prec->val++;
    }
    return 0;
}

/* parse 16-bit mask.
 * For each bit I write output either -1 if not set
 * or N if set.
 * N = the number of set bits >= I
 *
 * eg. A="0x5" (0b101) sets
 *  VALA = 2  # number of bits set
 *  VALB = 0
 *  VALC = -1
 *  VALD = 1
 *  VALE = -1
 *  ...
 *  VALQ = -1
 *
 *
record(asub, "$(N)") {
    field(SNAM, "asub_split_bits")
    field(FTA , "LONG")  # mask
    field(FTB , "ULONG") # Optional: reduce size of bitmask
    field(FTVA, "LONG")  # number of bits set
    field(FTVB, "LONG")  # -1 or number of bits set at or below
    ...
    field(FTVQ, "LONG")
}
 */
static
long asub_split_bits(aSubRecord *prec)
{
	/* By default support 12 channels */
	size_t ntmp = aSubRecordVALN - aSubRecordVALB;

	/* Optionally reduce bitmask size, if fewer channels supported */
    if ( prec->ftb==menuFtypeULONG ) {
		epicsUInt32 noutput = *(epicsUInt32*)prec->b;
		if ( (noutput > 0) && (noutput < ntmp) ) {
			ntmp = noutput;
		} 
	}
    const size_t nout = ntmp;

    epicsInt32 mask    = *(epicsInt32*)prec->a,
             *bitcnt   = prec->vala,
             **outputs = (epicsInt32**)&prec->valb;

    epicsUInt32 *outcnt = &prec->nevb;

    unsigned i;
    const epicsEnum16* outtype = &prec->ftvb;

    *bitcnt = 0;

    for(i=0; i<nout; mask<<=1, i++) {
        if(outtype[i]!=menuFtypeLONG)
            continue;

        if(mask&(1u<<(nout-1))) {
            *outputs[i] = (*bitcnt)++;

        } else {
            *outputs[i] = -1;
        }

        outcnt[i] = 1u;
    }

    prec->neva = 1;

    return 0;
}

/* parse <=32 bit mask (alternative to asub_split_bits)
 *
record(sub, "$(N)") {
    field(SNAM, "sub_feed_nset_bits")
    field(INPA, "mybit") # bit index
    field(INPB, "bitmask") # search in this bitmask
}
 * For bit index A:
 *  if A is not set in B, result is -1.
 *  if A is set, then result is number of set bits in B with an index less than B.
 *
 * eg.
 *  A=2 and B=5 (0b0111) yields 2
 *  A=2 and B=5 (0b0101) yields 1
 *  A=2 and B=4 (0b0100) yields 0
 *  A=2 and B=1 (0b0001) yields -1
 *  A=2 and B=8 (0b1000) yields -1
 */
static
long sub_feed_nset_bits(subRecord *prec)
{
    epicsUInt32 mybit = (unsigned long)prec->a;
    epicsUInt32 mymask = 1u<<mybit;
    epicsUInt32 bitmask = (unsigned long)prec->b;
    epicsInt32 nbits = -1;

    /* only count if mybit is set */
    if(bitmask & mymask) {
        /* count mybit, and lower */
        epicsUInt32 countmask = bitmask & (mymask | (mymask-1));

        for(;countmask; countmask>>=1) {
            if(countmask&1u)
                nbits++;
        }
    }

    prec->val = nbits;
    return 0;
}

/* Variant of sub_feed_nset_bits with reversed bitmask
record(sub, "$(N)") {
    field(SNAM, "sub_feed_nset_bits_rev")
    field(INPA, "mybit") # bit index
    field(INPB, "bitmask") # search in this bitmask
    field(INPC, "nbitmask") # Size of bitmask, must be < 32
}
*/
static
long sub_feed_nset_bits_rev(subRecord *prec)
{
    epicsUInt32 mybit = (unsigned long)prec->a;
    epicsUInt32 mymask = 1u<<mybit;
    epicsUInt32 bitmask = (unsigned long)prec->b;
    epicsUInt32 nbitmask = (unsigned long)prec->c;
    epicsInt32 nbits = -1;

    /* reverse mask */
    epicsUInt32 bitmask_rev = bitmask;
    int s = nbitmask - 1; // extra shift needed at end

    for (bitmask >>= 1; bitmask; bitmask >>= 1)
    {
        bitmask_rev <<= 1;
        bitmask_rev |= bitmask & 1;
        s--;
    }
    bitmask_rev <<= s; // shift when highest bits are zero
    bitmask_rev &= (1<<nbitmask)-1;

    /* only count if mybit is set */
    if(bitmask_rev & mymask) {
        /* count mybit, and lower */
        epicsUInt32 countmask = bitmask_rev & (mymask | (mymask-1));

        for(;countmask; countmask>>=1) {
            if(countmask&1u)
                nbits++;
        }
    }

    prec->val = nbits;
    return 0;
}

/* calculate shift and Y scaling factor
 * record(asub, "$(N)") {
 *   field(SNAM, "asub_yscale")
 *   field(FTA , "ULONG") # wave_samp_per register
 *   field(FTB , "ULONG") # cic_period
 *   field(FTVA, "ULONG") # wave_shift
 *   field(FTVB, "DOUBLE") # yscale
 * }
 */
static
long asub_yscale(aSubRecord *prec)
{
    const long shift_base = 4;
    const epicsUInt32 wave_samp_per = *(const epicsUInt32*)prec->a,
                      cic_period    = *(const epicsUInt32*)prec->b;
    epicsUInt32 *wave_shift = (epicsUInt32*)prec->vala;
    double *yscale = (double*)prec->valb;

    const double lo_cheat = (74762*1.646760258)/pow(2, 17);
    const epicsUInt32   cic_n    = wave_samp_per * cic_period;
    const double shift_min= log2(cic_n*cic_n * lo_cheat)-12;

    epicsInt32 wave_shift_temp = ceil(shift_min/2);
    if(wave_shift_temp<0)
        *wave_shift = 0;
    else
        *wave_shift = wave_shift_temp;

    *yscale = 16 * lo_cheat * (33 * wave_samp_per)*(33 * wave_samp_per) * pow(4, (8 - *wave_shift))/512.0/pow(2, shift_base);

    prec->udf = isnan(*yscale);

    return 0;
}

/* calculate shift and Y scaling factor for resonance system
 * record(asub, "$(N)") {
 *   field(SNAM, "asub_yscale")
 *   field(FTA , "ULONG") # wave_samp_per register
 *   field(FTB , "ULONG") # cic_period
 *   field(FTVA, "ULONG") # wave_shift
 *   field(FTVB, "DOUBLE") # yscale
 * }
 */
static
long asub_yscale_res(aSubRecord *prec)
{
	const epicsUInt32 wave_samp_per = *(const epicsUInt32*)prec->a,
						cic_period    = *(const epicsUInt32*)prec->b;
	epicsUInt32 *wave_shift = (epicsUInt32*)prec->vala;
	double *yscale = (double*)prec->valb;

	const epicsUInt32   cic_n    = wave_samp_per * cic_period;

	const int cic_order = 2;

	double bit_g = pow(cic_n, cic_order); // Bit-growth

	int wave_shift_temp = ceil(log2(bit_g)/cic_order); // FW accounts for cic_order when shifting

	if(wave_shift_temp<0)
		*wave_shift = 0;
	else
		*wave_shift = wave_shift_temp;

	double cic_gain = bit_g * pow(0.5, 2*(*wave_shift));

	*yscale = pow(2.0, 17) * cic_gain;

	prec->udf = isnan(*yscale);

	return 0;
}

/* calculate shift and Y scaling factor for injector system
 * record(asub, "$(N)") {
 *   field(SNAM, "asub_yscale")
 *   field(FTA , "ULONG") # wave_samp_per register
 *   field(FTB , "ULONG") # cic_period
 *   field(FTVA, "ULONG") # wave_shift
 *   field(FTVB, "DOUBLE") # yscale
 * }
 */
static
long asub_yscale_inj(aSubRecord *prec)
{
	const epicsUInt32 wave_samp_per = *(const epicsUInt32*)prec->a,
						cic_period    = *(const epicsUInt32*)prec->b;
	epicsUInt32 *wave_shift = (epicsUInt32*)prec->vala;
	double *yscale = (double*)prec->valb;

	const int cic_order = 2;

	// FW default shift assuming wsp = 1
	const epicsUInt32 shift_base = ceil(log2(pow(cic_period, cic_order)));

	// FW LO pre-scaling to cancel out non-unity CIC gain
        double pre_gain = 0.5  * pow(2.0, shift_base) / pow(cic_period, cic_order);

	const epicsUInt32 cic_n = wave_samp_per * cic_period;

	double bit_g = pow(cic_n, cic_order); // Bit-growth

	int bit_g_shift = ceil(log2(bit_g));

	int wave_shift_temp = (bit_g_shift - shift_base) / cic_order; // FW accounts for cic_order when shifting

	if(wave_shift_temp < 0)
		*wave_shift = 0;
	else
		*wave_shift = wave_shift_temp;

	double cic_gain = bit_g / pow(2.0, (cic_order*(*wave_shift) + shift_base));

	*yscale = pow(2.0, 19) * cic_gain * pre_gain;

	prec->udf = isnan(*yscale);

	return 0;
}

/* concatinate byte array together (bytes MSBF)
 *
 * record(asub, "$(N)") {
 *   field(SNAM, "asub_feed_bcat")
 *   field(FTA, "UCHAR") # byte array
 *   field(FTVA, "ULONG")# output word
 *   field(NEA , "3")    # max number of bytes
 * }
 */
static
long asub_feed_bcat(aSubRecord *prec)
{
    const epicsUInt8 *arr = (epicsUInt8*)prec->a;
    epicsUInt32 *out = (epicsUInt32*)prec->vala;
    epicsUInt32 i, lim = prec->nea;
    /* mask includes sign bit and all higher */
    epicsUInt32 mask = 0xffffffff<<(lim*8-1);

    *out = 0;

    for(i=0; i < lim; i++) {
        *out <<= 8;
        *out |= arr[i];
    }

    /* sign extend */
    if(mask & *out)
        *out |= mask;

    return 0;
}

static long
asub_round(aSubRecord *prec)
{
    double input = *(double *)prec->a;
    long *output = (long *)prec->vala;

    *output = (long)(round(input));
    
    return 0;

}

/* Ported from lcls2_llrf res_ctl.py. See cav_pzt.template for more info. 
 * (Resonance)
 */
static long
asub_pzt_src_set(aSubRecord *prec)
{

    /* Inputs */
    long src     = *(long *)prec->a; /* Source to set */
    long chan    = *(long *)prec->b; /* Channel(s) to set source for */
    long current = *(long *)prec->c; /* Latest reg value reading */

    /* Outputs */
    long *new = (long *)prec->vala; /* New register setting */

    /* Intermediate values */
    long mask, dismask;

    short debug = (prec->tpro > 1) ? 1 : 0;

    /* Get mask for correct source */
    switch(src) {
	case 0:
	    mask = 0x0;
	    break;
	case 1:
	    mask = 0x1;
	    break;
	case 2:
	    mask = 0x2;
	    break;
	default:
	    if (debug) {
		printf("asub_pzt_src_set: %s Source %li not recognized. "
			"Must be 0, 1, or 2.\n", prec->name, src);
	    }
	    (void)recGblSetSevr(prec, CALC_ALARM, INVALID_ALARM);
	    return EINVAL;
    }

    /* Choose which piezo channel to get source */
    switch(chan) {
	case 0:
            mask = (mask << 2) | mask;
            dismask = 0xf;
	    break;
	case 1:
            mask = mask;
            dismask = 0x3;
	    break;
	case 2:
            mask = mask << 2;
            dismask = 0x3 << 2;
	    break;
	default:
	    if (debug) {
		printf("asub_pzt_src_set: %s Chan %li selection not recognized. "
			"Must be 0, 1, or 2.\n", prec->name, src);
	    }
	    (void)recGblSetSevr(prec, CALC_ALARM, INVALID_ALARM);
	    return EINVAL;
    }

    /* Get current value and write-back value with correct bits set */
    *new = (~(dismask) & current) | mask;

    if (debug) {
	printf("asub_pzt_src_set: %s Source %li chan %li current %li " 
		"mask %li dismask %li new %li\n", prec->name, src, 
		chan, current, mask, dismask, *new);
    }


    return 0;
}

/* (Resonance) */
static long
asub_pzt_src_get(aSubRecord *prec)
{

    /* Inputs */
    long chan    = *(long *)prec->a; /* Channel(s) to get source for; 0 for A, 1 for B */
    long current = *(long *)prec->b; /* Latest reg value reading */

    /* Outputs */
    long *src = (long *)prec->vala; /* Current source setting for this channel */

    /* Intermediate values */
    int shift;

    short debug = (prec->tpro > 1) ? 1 : 0;

    switch(chan) {
	case 0:
	    shift = 0;
	    break;
	case 1:
	    shift = 2;
	    break;
	default:
	    if (debug) {
		printf("asub_pzt_src_get: %s Channel %li not recognized. "
			"Must be 0 for ch A or 1 for ch B.\n", prec->name, chan);
	    }
	    (void)recGblSetSevr(prec, CALC_ALARM, INVALID_ALARM);
	    return EINVAL;
    }

    *src = (current & (0x3<<shift)) >> shift;

    if (debug) {
	printf("asub_pzt_src_get: %s chan %li current %li output src %li\n",
		prec->name, chan, current, *src);
    }

    return 0;
}

/* Extract unsigned integer from word (Currently used only in resonance) */
static long
asub_mask(aSubRecord *prec)
{
    epicsUInt32 input =  *(epicsUInt32 *)prec->a,
		mask   = *(epicsUInt32 *)prec->b,
		lshift = *(epicsUInt32 *)prec->c,
		rshift = *(epicsUInt32 *)prec->d;

    epicsUInt32 *output = (epicsUInt32 *)prec->vala;

    short debug = (prec->tpro > 1) ? 1 : 0;

    *output = (input & (mask << lshift)) >> rshift;

    if (debug) {
	printf("asub_mask: %s input %u mask %u lshift %u rshift %u output %u\n",
		prec->name, input, mask, lshift, rshift, *output);
	printf("asub_mask: (mask << lshift)) %u (input & (mask << lshift)) %u\n", (mask << lshift), (input & (mask << lshift)));
    }

    return 0;
}

/* Convert to signed number. (Currently used only in resonance)
 * Optionally apply linear scaling, scale and/or offset: 
 *  INPC = scale
 *  INPD = offset 
 */
static long
asub_signed(aSubRecord *prec)
{
    epicsUInt32 input =  *(epicsUInt32 *)prec->a,
		nbits =  *(epicsUInt32 *)prec->b; /* Number of bits of signed integer--
						   * counting sign bit 
						   */
    double *output = (double *)prec->vala;

    short debug = (prec->tpro > 1) ? 1 : 0;

    *output = (double)((input > (pow(2,nbits)/2 - 1)) ? input - pow(2,nbits) : input);

    if (debug) {
	printf("asub_signed: %s input %u nbits %u output %f\n",
		prec->name, input, nbits, *output);
    }

    if ( prec->ftc==menuFtypeDOUBLE ) {
	double scale = *(double *)prec->c;
	if (scale != 0) {
	    *(double *)prec->valb = *output * scale;
	    if (debug) {
		printf("asub_signed: %s applied scale factor %f new value %f\n",
		    prec->name, scale, *(double *)prec->valb);
	    }
	}
    }

    if ( prec->ftd==menuFtypeDOUBLE ) {
	double offset = *(double *)prec->d;
	if (offset != 0) {
	    *(double *)prec->valb =  *(double *)prec->valb + offset;
	    if (debug) {
		printf("asub_signed: %s applied offset %f new value %f\n",
		    prec->name, offset, *(double *)prec->valb);
	    }
	}
    }

    return 0;
}

/* Calculate quench detection coefficients and threshold (RFS) */
static long
asub_quench(aSubRecord *prec)
{
    short debug = (prec->tpro > 1) ? 1 : 0;

	double cav_scale   = *(double *)prec->a,
	       fwd_scale   = *(double *)prec->b,
	       rev_scale   = *(double *)prec->c,
	       fullscale_w = *(double *)prec->d,
	       freq        = *(double *)prec->e, /* cavity frequency */
	       imped       = *(double *)prec->f, /* shunt impedance R/Q */
	       thresh_w    = *(double *)prec->g; /* quench trip threshold */

	double filter_gain = (double)*(epicsUInt32 *)prec->h; /* Digaree FIR filter gain */

	double *consts = (double *)prec->vala,
	       *fullscale_w_inuse = (double *)prec->valc;
	short  *override = (short *)prec->valb;
	unsigned nelm = 4, i;
	double max;

	double freq_rad = 2 * PI * freq,
	       dt = 32 * 33 * 14 / 1320e6,
	       dudt_scale  = 16;

	double denom = freq_rad * imped * dt * filter_gain * dudt_scale;

	*fullscale_w_inuse = fullscale_w;
	*override = 0;

    if(prec->nova != nelm) {
    	if(debug)
        	errlogPrintf("%s nova must be 4 but is %u\n", prec->name, (unsigned)prec->nova);
        (void)recGblSetSevr(prec, CALC_ALARM, INVALID_ALARM);
	}

	if (debug) {
		printf("asub_quench: %s\n     inputs: cav_scale %.1f fwd_scale %.1f rev_scale %.1f\n"
			"         fullscale_w %.1f freq %.1f R/Q %.1f thresh_w %.1f filter_gain %.1f\n",
			prec->name, cav_scale, fwd_scale, rev_scale, fullscale_w, freq, imped, thresh_w, filter_gain);
	}

	consts[0] = pow(rev_scale,2);
	consts[1] = pow(fwd_scale,2);
	consts[2] = pow(cav_scale * 1e6, 2) / denom;
	consts[3] = thresh_w;

	if (debug) {
		printf("     full-scale will be max of rev %.1f fwd %.1f cav %.1f thresh %.1f and fullscale_w\n",
			consts[0], consts[1], consts[2], consts[3]);
	}

	max = 1.001 * MAX(consts[0], MAX(consts[1], MAX(consts[2], consts[3])));
	if (max > fullscale_w) {
		*fullscale_w_inuse = max;
		*override = 1;
		if (debug) {
			printf("     Overriding input full-scale value. Using %.1f.\n", *fullscale_w_inuse);
		}
	}

	if (debug) {
		printf("     intermediate values: dt %.3e dudt_scale %.1f denom %.1f\n",
			dt, dudt_scale, denom);
	}

	for (i = 0; i < nelm; i++) {
		consts[i] = consts[i] / *fullscale_w_inuse;
		if (debug) {
    		printf("     normalized constant array element %i %.5f\n", i, consts[i]);
		}
    	if((consts[i] >= 1.0) || (consts[i] <= 0.0) || (isnan(consts[i]))) {
    		if(debug)
        		errlogPrintf("%s const index %i value %.5f illegal value\n", prec->name, i, consts[i]);
        	(void)recGblSetSevr(prec, CALC_ALARM, INVALID_ALARM);
        	return EINVAL;
		}
		consts[i] = floor(consts[i] * pow(2,19));
	}

	if (debug) {
		printf("     final output array: rev %.0f fwd %.0f cav %.0f thres %.0f\n",
			consts[0], consts[1], consts[2], consts[3]);
	}

    return 0;
}

static
void asubFEEDRegistrar(void)
{
    registryFunctionAdd("asub_feed_timebase", (REGISTRYFUNCTION)&asub_feed_timebase);
    registryFunctionAdd("asub_split_bits", (REGISTRYFUNCTION)&asub_split_bits);
    registryFunctionAdd("sub_count_bits", (REGISTRYFUNCTION)&sub_count_bits);
    registryFunctionAdd("asub_yscale", (REGISTRYFUNCTION)&asub_yscale);
    registryFunctionAdd("asub_yscale_res", (REGISTRYFUNCTION)&asub_yscale_res);
    registryFunctionAdd("asub_yscale_inj", (REGISTRYFUNCTION)&asub_yscale_inj);
    registryFunctionAdd("sub_feed_nset_bits", (REGISTRYFUNCTION)&sub_feed_nset_bits);
    registryFunctionAdd("sub_feed_nset_bits_rev", (REGISTRYFUNCTION)&sub_feed_nset_bits_rev);
    registryFunctionAdd("asub_feed_bcat", (REGISTRYFUNCTION)&asub_feed_bcat);
    registryFunctionAdd("asub_round", (REGISTRYFUNCTION)&asub_round);
    registryFunctionAdd("asub_pzt_src_set", (REGISTRYFUNCTION)&asub_pzt_src_set);
    registryFunctionAdd("asub_pzt_src_get", (REGISTRYFUNCTION)&asub_pzt_src_get);
    registryFunctionAdd("asub_mask", (REGISTRYFUNCTION)&asub_mask);
    registryFunctionAdd("asub_signed", (REGISTRYFUNCTION)&asub_signed);
    registryFunctionAdd("asub_quench_coef", (REGISTRYFUNCTION)&asub_quench);
}
epicsExportRegistrar(asubFEEDRegistrar);
