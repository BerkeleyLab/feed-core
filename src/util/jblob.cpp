
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <list>
#include <string.h>

#include <errlog.h>
#include <yajl_parse.h>

#include <epicsStdlib.h>

#include "utils.h"
#include "jblob.h"

namespace {

// undef implies API version 0
#ifndef EPICS_YAJL_VERSION
typedef long integer_arg;
typedef unsigned size_arg;
#else
typedef long long integer_arg;
typedef size_t size_arg;
#endif

struct context {
    JBlob blob;

    std::string err, // error message
                regname,
                param;
    unsigned depth;
    bool in_metadata;

    bool ignore_scratch;
    JRegister scratch;

    void warn(const std::string& msg) {
        errlogPrintf("FEED JSON warning: %s\n", msg.c_str());
    }

    context() :depth(0), in_metadata(false), ignore_scratch(false) {}
};

#define TRY context *self = static_cast<context*>(ctx); try

#define CATCH() catch(std::exception& e) { if(self->err.empty()) self->err = e.what(); return 0; }

int jblob_null(void *ctx)
{
    TRY {
        self->warn("ignoring unsupported: null");
        return 1;
    }CATCH()
}

int jblob_boolean(void *ctx, int val)
{
    TRY {
        self->warn(SB()<<"ignoring unsupported: boolean value "<<val);
        return 1;
    }CATCH()
}

int jblob_integer(void *ctx, integer_arg val)
{
    TRY {
        if(self->depth==2) {
            if(self->in_metadata) {
                self->blob.info32[self->param] = val;

            } else if(self->param=="base_addr") {
                if(val&0xff000000) {
                    self->ignore_scratch = true;
                    self->warn(SB()<<self->regname<<"."<<self->param<<" ignores out of range base_addr");
                } else {
                    self->scratch.base_addr = val;
                }

            } else if(self->param=="addr_width") {
                if(val>32) {
                    self->ignore_scratch = true;
                    self->warn(SB()<<self->regname<<"."<<self->param<<" ignores out of range addr_width");
                } else {
                    self->scratch.addr_width = val;
                }

            } else if(self->param=="data_width") {
                if(val>32) {
                    self->ignore_scratch = true;
                    self->warn(SB()<<self->regname<<"."<<self->param<<" ignores out of range data_width");
                } else {
                    self->scratch.data_width = val;
                }

            } else {
                self->warn(SB()<<self->regname<<"."<<self->param<<" ignores integer value");
            }
        } else
            self->warn(SB()<<"ignored integer value at depth="<<self->depth);
        return 1;
    }CATCH()
}

int jblob_double(void *ctx, double val)
{
    TRY {
        self->warn(SB()<<"ignoring unsupported: double value "<<val);
        return 1;
    }CATCH()
}

int jblob_string(void *ctx, const unsigned char *val, size_arg len)
{
    TRY {
        std::string V((const char*)val, len);

        if(self->depth==2) {
            if(self->in_metadata) {
                // TODO handle string metadata?
                // until then, silently ignore as this might be interesting
                // to scripts
            } else if(self->param=="access") {
                self->scratch.readable = V.find_first_of('r')!=V.npos;
                self->scratch.writable = V.find_first_of('w')!=V.npos;

            } else if(self->param=="description") {
                self->scratch.description = V;

            } else if(self->param=="sign") {
                if(V=="unsigned") {
                    self->scratch.sign = JRegister::Unsigned;

                } else if(V=="signed") {
                    self->scratch.sign = JRegister::Signed;

                } else {
                    self->warn(SB()<<self->regname<<"."<<self->param<<" unknown value "<<V<<" assume Unsigned");
                }

            } else {
                // try to parse any unknown strings as integers
                epicsInt32 val = 0;
                if(epicsParseInt32(V.c_str(), &val, 0, 0)) {
                    self->warn(SB()<<self->regname<<"."<<self->param<<" unable to parse string value '"<<V<<"' as integer");

                } else {
                    return jblob_integer(ctx, val);
                }
            }
        } else
            self->warn(SB()<<"ignored string value at depth="<<self->depth);
        return 1;
    }CATCH()
}

int jblob_start_map(void *ctx)
{
    TRY {
        self->depth++;
        if(self->depth==2)
            self->ignore_scratch = false; // starting a new register
        if(self->depth>2) {
            throw std::runtime_error("Object depth limit (2) exceeded");
        }
        return 1;
    }CATCH()
}

int jblob_map_key(void *ctx, const unsigned char *key, size_arg len)
{
    TRY {
        if(len==0)
            throw std::runtime_error("Zero length key not allowed");
        std::string K((const char*)key, len);
        if(self->depth==1) {
            self->regname = K;
            if(self->regname=="__metadata__") {
                self->in_metadata = true;
            } else
            if(self->blob.registers.find(K)!=self->blob.registers.end()) {
                self->warn(SB()<<"Duplicate definition for register "<<self->regname);
            }
        } else if(self->depth==2) {
            self->param = K;
        } else {
            throw std::logic_error("key at unsupported depth");
        }
        return 1;
    }CATCH()
}

int jblob_end_map(void *ctx)
{
    TRY {
        if(self->depth==2) {
            if(self->ignore_scratch) {
                self->warn(SB()<<"Ignore illformed definition for register "<<self->regname);

            } else {
                // ignore register definitions when some important part was incorrectly formatted
                self->scratch.name = self->regname;
                self->blob.registers[self->regname] = self->scratch;
            }
            self->ignore_scratch = false;
            self->in_metadata = false;
            self->scratch.clear();
        }
        if(self->depth==0)
            throw std::logic_error("Object depth underflow");
        self->depth--;
        return 1;
    }CATCH()
}

yajl_callbacks jblob_cbs = {
    &jblob_null, // null
    &jblob_boolean, // boolean
    &jblob_integer,
    &jblob_double, // double
    NULL, // number
    &jblob_string,
    &jblob_start_map,
    &jblob_map_key,
    &jblob_end_map,
    NULL, // start array
    NULL, // end array
};

struct handler {
    yajl_handle handle;
    explicit handler(yajl_handle handle) :handle(handle)
    {
        if(!handle)
            throw std::runtime_error("Failed to allocate yajl handle");
    }
    ~handler() {
        yajl_free(handle);
    }
    operator yajl_handle() { return handle; }
};

} // namespace

void JBlob::parseFile(const char *name)
{
    parse(read_entire_file(name).c_str());
}

void JBlob::parse(const char *buf)
{
    parse(buf, strlen(buf));
}

void JBlob::parse(const char *buf, size_t buflen)
{
#ifndef EPICS_YAJL_VERSION
    yajl_parser_config conf;
    memset(&conf, 0, sizeof(conf));
    conf.allowComments = 1;
    conf.checkUTF8 = 1;
#endif

    context ctxt;

#ifndef EPICS_YAJL_VERSION
    handler handle(yajl_alloc(&jblob_cbs, &conf, NULL, &ctxt));
#else
    handler handle(yajl_alloc(&jblob_cbs, NULL, &ctxt));
#endif

    yajl_status sts = yajl_parse(handle, (const unsigned char*)buf, buflen);
#ifndef EPICS_YAJL_VERSION
    if(sts==yajl_status_insufficient_data) {
        sts = yajl_parse_complete(handle);
    }
#else
    if(sts==yajl_status_ok)
        sts = yajl_complete_parse(handle);
#endif
    switch(sts) {
    case yajl_status_ok:
        break;
    case yajl_status_error: {
        std::string msg;
        unsigned char *raw = yajl_get_error(handle, 1, (const unsigned char*)buf, buflen);
        try {
            msg = (char*)raw;
            yajl_free_error(handle, raw);
        }catch(...){
            yajl_free_error(handle, raw);
            throw;
        }
        throw std::runtime_error(msg);
    }
    case yajl_status_client_canceled:
        throw std::runtime_error(ctxt.err);
#ifndef EPICS_YAJL_VERSION
    case yajl_status_insufficient_data:
        throw std::runtime_error("Unexpected end of input");
#endif
    }

    registers.swap(ctxt.blob.registers);
    info32.swap(ctxt.blob.info32);
}

const JRegister& JBlob::operator[](const std::string& name) const
{
    const_iterator it(find(name));
    if(it==registers.end())
        throw std::runtime_error("No such register");
    return it->second;
}

std::ostream& operator<<(std::ostream& strm, const JBlob& blob)
{
    strm<<"{";
    bool first=true;
    for(JBlob::registers_t::const_iterator it=blob.registers.begin(), end=blob.registers.end();
        it!=end; ++it)
    {
        if(first) first=false;
        else strm<<", ";
        strm<<"\""<<it->first<<"\":"<<it->second;
    }
    strm<<"}";
    return strm;
}

std::ostream& operator<<(std::ostream& strm, const JRegister& reg)
{
    strm<<"{"
          "\"access\":\""<<(reg.readable?"r":"")<<(reg.writable?"w":"")<<"\", "
          "\"addr_width\":"<<unsigned(reg.addr_width)<<", "
          "\"base_addr\":"<<reg.base_addr<<", "
          "\"data_width\":"<<unsigned(reg.data_width)<<", "
          "\"description\":\""<<reg.description<<"\", "
          "\"sign\":\""<<(reg.sign==JRegister::Unsigned?"un":"")<<"signed\""
          "}";
    return strm;
}


epicsInt64 JRegister::min() const {
    if(sign==Unsigned) {
        return 0;
    } else {
        epicsUInt64 signmask = 0;
        signmask = 0xffffffffffffffff << (data_width-1);
        return (epicsInt64)signmask;
    }
}
epicsInt64 JRegister::max() const
{
    unsigned nbits = data_width;
    if(sign==Signed)
        nbits--;
    return (epicsInt64(1)<<nbits)-1;
}
