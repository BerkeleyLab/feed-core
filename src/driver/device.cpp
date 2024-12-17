#include <stdexcept>
#include <iostream>
#include <sstream>
#include <algorithm>

#include <poll.h>

#include <errlog.h>
#include <alarm.h>
#include <dbAccess.h>
#include <recSup.h>
#include <epicsExit.h>

#include "device.h"
#include "zpp.h"
#include "rom.h"

// max number of concurrent requests
int feedNumInFlight = 1;
// timeout for reply (in sec.)
double feedTimeout = 1.0;
// Size of IP and UDP headers.
// I don't know how to determine this programatically, so make it configurable.
int feedUDPHeaderSize = 42;

namespace {
const size_t pkt_size_limit = (DevMsg::nreg+1)*8;

// description of automatic/bootstrap registers
const struct gblrom_t {
    JRegister jrom2_info, jrom16_info;
    JRegister jid_info;
    gblrom_t() {
        jid_info.name = "HELLO";
        jid_info.description = "Hello World!";
        jid_info.addr_width = 2; // 4 words
        jid_info.base_addr = 0;
        jid_info.data_width = 32;
        jid_info.readable = true;

        // N.B: Newer devices have a relocated ROM at address 0x4000. On these,
        // 2K aperture at 0x800 is guaranteed to be 0x0 and not decode to a
        // valid ROM. Thus, we first attempt to parse the ROM at the original
        // 0x800 location and move on to 0x4000 if unsuccessful.

        // TODO: A useful optimization would be to only avoid reading null data
        // to minimize traffic over the wire
        jrom2_info.name = "ROM 2K";
        jrom2_info.description = "Static configuration";
        jrom2_info.base_addr = 0x800;
        jrom2_info.addr_width = 11; // 2048 words
        jrom2_info.data_width = 16;
        jrom2_info.readable = true;

        jrom16_info.name = "ROM 16K";
        jrom16_info.description = "Static configuration";
        jrom16_info.base_addr = 0x4000;
        jrom16_info.addr_width = 14; // 16384 words
        jrom16_info.data_width = 16;
        jrom16_info.readable = true;
    }
} gblrom;
}

RegInterest::RegInterest(dbCommon *prec, Device *dev)
    :prec(prec)
    ,device(dev)
    ,reg(0)
{
    scanIoInit(&changed);
}

#define IFDBG(N, FMT, ...) if(dev->debug&(1u<<(N))) errlogPrintf("%s %s : " FMT "\n", logTime(), dev->myname.c_str(), __VA_ARGS__)

DevReg::DevReg(Device *dev, const JRegister &info, bool bootstrap)
    :dev(dev)
    ,info(info)
    ,bootstrap(bootstrap)
    ,state(Invalid)
    ,read_queued(false)
    ,write_queued(false)
    ,mem_rx(1u<<info.addr_width, 0)
    ,mem_tx(1u<<info.addr_width, 0)
    ,received(1u<<info.addr_width, false)
    ,nremaining(0u)
    ,next_send(mem_rx.size())
    ,stat(UDF_ALARM)
    ,sevr(INVALID_ALARM)
{}

DevReg::~DevReg()
{
    reset();
}

void DevReg::reset()
{
    state = DevReg::Invalid;
    read_queued = write_queued = false;

    // shouldn't be letting these fall on the floor...
    assert(records_inprog.empty());
    assert(records_write.empty());
    assert(records_read.empty());
}

void DevReg::process(bool cancel)
{
    // in-progress reads/writes
    dev->records.splice(dev->records.end(),
                        records_inprog);

    if(cancel) {
        // for queued write
        dev->records.splice(dev->records.end(),
                            records_write);

        // for queued read
        dev->records.splice(dev->records.end(),
                            records_read);
    }
}

void DevReg::scan_interested()
{
    for(interested_t::const_iterator it = interested.begin(),
        end = interested.end();
        it != end; ++it)
    {
        assert((*it)->reg = this);

        scanIoRequest((*it)->changed);
    }
}

void DevReg::queue(bool write, RegInterest *action)
{
    switch(state) {
    case Invalid:
    case InSync:
        // Idle, queue immediately

        if((!write && !info.readable)
                || (write && !info.writable))
            throw std::runtime_error("Register does not support requested operation");

        // reset address tracking
        std::fill(received.begin(),
                  received.end(),
                  false);
        nremaining = received.size();
        next_send = 0;

        dev->reg_send.push_back(this);

        state = write ? Writing : Reading;

        if(action)
            records_inprog.push_back(action);

        dev->poke_runner();

        IFDBG(5, "queue %s for %s from %06x",
                     info.name.c_str(),
                     write ? "write" : "read",
                     (unsigned)next_send);
        break;
    case Writing:
        // write in progress, flag to re-queue on completion
        if(write) {
            if(action)
                records_write.push_back(action);
            write_queued = true;
        } else {
            if(action)
                records_read.push_back(action);
            read_queued = true;
        }
        break;
    case Reading:
        // read in progress
        if(write) {
            // flag to queue write after read completes
            if(action)
                records_write.push_back(action);
            write_queued = true;
        } else {
            // merge this read request with the inprogress op
            if(action)
                records_inprog.push_back(action);
        }
        break;
    }
}

#undef IFDBG

Device::devices_t Device::devices;

const char *Device::current_name[5] = {
    "Error",
    "Idle",
    "Searching",
    "Inspecting",
    "Running",
};

static void feed_shutdown(void *raw)
{
    Device *dev = static_cast<Device*>(raw);

    {
        Guard G(dev->lock);
        dev->runner_stop = true;
    }
    dev->poke_runner();
    dev->runner.exitWait();
}

#define IFDBG(N, FMT, ...) if(debug&(1u<<(N))) errlogPrintf("%s %s : " FMT "\n", logTime(), myname.c_str(), ##__VA_ARGS__)

Device::Device(const std::string &name, osiSockAddr &ep)
    :sock(AF_INET, SOCK_DGRAM, 0)
    ,myname(name)
    ,debug(0xffffffff)
    ,current(Idle)
    ,cnt_sent(0u)
    ,cnt_recv(0u)
    ,cnt_recv_bytes(0u)
    ,cnt_ignore(0u)
    ,cnt_timo(0u)
    ,cnt_err(0u)
    ,rtt_ptr(0u)
    ,reg_rom2(new DevReg(this, gblrom.jrom2_info, true))
    ,reg_rom16(new DevReg(this, gblrom.jrom16_info, true))
    ,reg_id(new DevReg(this, gblrom.jid_info, true))
    ,inflight(std::max(1, std::min(feedNumInFlight, 255))) // limit to [0, 255] as we choose to encode offset in request header
    ,want_to_send(false)
    ,runner_stop(false)
    ,reset_requested(false)
    ,error_requested(false)
    ,after_reset(false)
    ,runner(*this,
            "FEED",
            epicsThreadGetStackSize(epicsThreadStackSmall),
            epicsThreadPriorityHigh)
{
    memset(&peer_addr, 0, sizeof(peer_addr));

    roundtriptimes.resize(100);

    epicsTimeStamp now;
    epicsTimeGetCurrent(&now);
    // pseudo-random initial sequence number
    send_seq = now.nsec;

    scanIoInit(&on_connect);
    scanIoInit(&current_changed);
    last_message = "Startup";

    sock.set_blocking(false);
    sock.bind(ep);

    Socket::pipe(wakeupRx, wakeupTx);

    // make non-blocking so we can safely poke_runner() w/ lock held
    wakeupTx.set_blocking(false);

    reset();

    epicsAtExit(feed_shutdown, this);
}

Device::~Device()
{
    // never free'd
    assert(false);
}

void Device::poke_runner()
{
    wakeupTx.trysend("!", 1);
}

void Device::request_reset()
{
    reset_requested = true;
    poke_runner();
}

void Device::reset(bool error)
{
    if(error) {
        IFDBG(0, "External Error signaled: %s", last_message.c_str());
    } else {
        IFDBG(0, "reset w/ %s", peer_name.c_str());
    }

    want_to_send = false;
    reset_requested = false;
    error_requested = false;
    after_reset = true;

    if(error) {
        current = Error;
    } else if(peer_name.empty()) {
        current = Idle;
    } else {
        current = Searching;
    }

    // forget about pending or Sent messages
    for(size_t i=0, N=inflight.size(); i<N; i++)
    {
        inflight[i].clear();
    }

    reg_send.clear();

    for(reg_by_name_t::const_iterator it = reg_by_name.begin(), end = reg_by_name.end();
        it != end; ++it)
    {
        DevReg *reg = it->second;

        // put all register contents into a known state
        // on disconnect.
        std::fill(reg->mem_rx.begin(),
                  reg->mem_rx.end(),
                  0);
        std::fill(reg->mem_tx.begin(),
                  reg->mem_tx.end(),
                  0);

        // complete any in-progress async, including for queued writes
        reg->stat = COMM_ALARM;
        reg->sevr = INVALID_ALARM;
        reg->process(true);

        if(!reg->bootstrap) {
            delete reg;
        } else {
            reg->reset();
        }
    }

    // restart with only automatic/bootstrap registers
    reg_by_name.clear();
    reg_by_name[reg_id->info.name] = reg_id.get();
    reg_by_name[reg_rom2->info.name] = reg_rom2.get();
    reg_by_name[reg_rom16->info.name] = reg_rom16.get();

    if(!error) {
        last_message.clear();
    }
    dev_infos.clear();
    description.clear();
    jsonhash.clear();
    codehash.clear();
    info32.clear();

    for(reg_interested_t::const_iterator it = reg_interested.begin(), end = reg_interested.end();
        it != end; ++it)
    {
        if(it->second->reg && it->second->reg->bootstrap)
            continue;

        // break association with (now deleted) register
        it->second->reg = 0;
        scanIoRequest(it->second->changed);
    }

    scanIoRequest(current_changed);
}

void Device::handle_send(Guard& G)
{
    const epicsTime due(loop_time + feedTimeout);

    // first pass to populate DevMsg
    for(size_t i=0, N=inflight.size(); i<N && !reg_send.empty(); i++)
    {
        DevMsg& msg = inflight[i];
        if(msg.state==DevMsg::Sent)
            continue;
        // found available message slot

        for(unsigned j=0; j<DevMsg::nreg && !reg_send.empty(); j++) {
            if(msg.reg[j])
                continue;

            DevReg *R = reg_send.front();

            assert(R->inprogress());
            assert(R->next_send < R->mem_tx.size() );

            // found available address slot in message

            msg.buf.resize(2*j + 4);

            epicsUInt32 offset = R->next_send++;
            epicsUInt32 addr = R->info.base_addr + offset;
            epicsUInt32 val = 0;

            if(R->state==DevReg::Reading) {
                addr |= 0x10000000;

            } else {
                val = R->mem_tx.at(offset);
            }

            msg.reg[j] = R;
            msg.buf[2*j + 2] = htonl(addr);
            msg.buf[2*j + 3] = val;

            if(R->next_send>=R->mem_tx.size()) {
                // all addresses of this register have been sent
                reg_send.pop_front();
            }
        }

        if(msg.reg[0]) {
            msg.state = DevMsg::Ready;
        }
    }

    // second pass to send any Ready
    unsigned nsent=0;
    for(size_t i=0, N=inflight.size(); i<N; i++)
    {
        DevMsg& msg = inflight[i];
        if(msg.state!=DevMsg::Ready)
            continue;

        // some devices require a minimum message length
        while(msg.buf.size()<8) {
            // pad with reads of offset zero ("Hell" register)
            msg.buf.push_back(htonl(0x10000000));
            msg.buf.push_back(0);
        }

        // encode both message slot offset (to simplify our RX processing)
        // and a sequence number (to reject duplicate/late messages)
        msg.seq = (i<<24) | ((send_seq++)&0x00ffffff);

        msg.buf[0] = htonl(0xfeedc0de);
        msg.buf[1] = htonl(msg.seq);

        try {
            // non-blocking sendto(), so we don't unlock here
            sock.sendto(peer_addr, (const char*)&msg.buf[0], msg.buf.size()*4);
            cnt_sent++;
        }catch(SocketError& e){
            if(e.code==SOCK_EWOULDBLOCK) {
                want_to_send = true;
                return;
            } else if(e.code==ENETUNREACH || e.code==EHOSTUNREACH) {
                IFDBG(1, "Unable to send to %s : (%d) %s", peer_name.c_str(), e.code, e.what());
                // Don't throw (and latch into Error state) what is probably
                // a transient error.  Will timeout since packet wasn't sent
            } else {
                throw;
            }
        }
        IFDBG(1, "Send seq=%08x %zu bytes", (unsigned)msg.seq, msg.buf.size()*4u);

        msg.due = due;
        msg.state = DevMsg::Sent;
        nsent++;
    }

    IFDBG(4, "Sent %u messages", nsent);
}

void Device::handle_process(const std::vector<char>& buf, PrintAddr& addr)
{
    // check for minimum message size
    if(buf.size()<8u*4u) {
        cnt_ignore++;
        IFDBG(0, "Ignore short %zu byte message from %s", buf.size(), addr.c_str());
        return;
    }

    const epicsUInt32 *ibuf = (const epicsUInt32*)&buf[0];
    const size_t ilen = buf.size()/4;

    epicsUInt32 seq = ntohl(ibuf[1]);
    epicsUInt8 off = seq>>24;

    IFDBG(1, "Recv seq=%08x %zu bytes", (unsigned)seq, buf.size());

    if(ntohl(ibuf[0])!=0xfeedc0de || off>=inflight.size()) {
        cnt_ignore++;
        IFDBG(0, "Ignore corrupt message from %s (%08x %08x)", addr.c_str(),
                     (unsigned)ibuf[0], (unsigned)ibuf[1]);
        return;

    } else if(inflight[off].state!=DevMsg::Sent) {
        IFDBG(0, "Duplicate ignored seq=%08x", (unsigned)seq);
        cnt_ignore++;
        return;

    } else if(inflight[off].seq != seq) {
        cnt_ignore++;
        IFDBG(0, "Ignore stale/duplicate message from %s (%08x)", addr.c_str(), (unsigned)ibuf[0]);
        return;
    }

    DevMsg& msg = inflight[off];

    for(unsigned j=0; j<DevMsg::nreg; j++) {
        if(!msg.reg[j] || !msg.reg[j]->inprogress())
            continue;

        DevReg * const reg = msg.reg[j];

        if(j*2+3 >= ilen) {
            IFDBG(0, "reply truncated %zu expected %zu", ilen*4, msg.buf.size()*4);
            do_timeout(off);
            continue;

        }else if((ibuf[j*2 + 2]&htonl(0xf0ffffff))!=msg.buf[j*2+2]) {
            // we don't expect re-ordering or change in command type
            // but allow 4 bits don't-care as future status bits.
            IFDBG(0, "response type doesn't match request (%08x %08x)",
                         (unsigned)ibuf[j*2 + 2], (unsigned)msg.buf[j*2+2]);
            do_timeout(off);
            continue;
        }

        epicsUInt32 cmd_addr = ntohl(ibuf[j*2 + 2]),
                data     = ibuf[j*2 + 3];

        epicsUInt32 offset = (cmd_addr&0x00ffffff) - reg->info.base_addr;

        if(cmd_addr&0x10000000) {
            reg->mem_rx.at(offset) = data;
        } else {
            // writes simply echo written value, ignore data
        }

        if(!reg->received.at(offset)) {
            reg->received[offset] = true;
            reg->nremaining--;
        }

        if(!reg->nremaining)
        {
            assert(std::find(reg->received.begin(),
                             reg->received.end(),
                             false) == reg->received.end());

            // all addresses received
            reg->state = DevReg::InSync;

            // register timestamp is the time when this last packet is received.
            reg->rx = loop_time;

            reg->stat = 0;
            reg->sevr = 0;
            reg->process(false);

            reg->scan_interested();
            IFDBG(5, "complete %s", reg->info.name.c_str());

            if(reg->write_queued) {
                reg->write_queued = false;
                reg->records_inprog.splice(reg->records_inprog.end(),
                                           reg->records_write);
                reg->queue(true);
                IFDBG(5, "start queued write %s", reg->info.name.c_str());

            } else if(reg->read_queued) {
                reg->read_queued = false;
                reg->records_inprog.splice(reg->records_inprog.end(),
                                           reg->records_read);
                reg->queue(false);
                IFDBG(5, "start queued read %s", reg->info.name.c_str());
            }

        }

        msg.reg[j] = 0;
    }

    roundtriptimes[rtt_ptr] = loop_time-msg.due+feedTimeout;
    rtt_ptr = (rtt_ptr+1)%roundtriptimes.size();

    msg.clear();
}

void Device::handle_timeout()
{
    for(size_t i=0, N=inflight.size(); i<N; i++)
    {
        DevMsg& msg = inflight[i];
        if(msg.state!=DevMsg::Sent || msg.due>loop_time)
            continue;

        IFDBG(1, "timeout seq=%08x", (unsigned)msg.seq);

        do_timeout(i);
    }
}

void Device::do_timeout(unsigned i)
{
    DevMsg& msg = inflight[i];
    // timeout!
    cnt_timo++;

    // Full reset following any timeout
    reset_requested = true;

    for(unsigned j=0; j<DevMsg::nreg; j++)
    {
        if(!msg.reg[j])
            continue;
        DevReg *reg = msg.reg[j];

        assert(reg->inprogress());

        IFDBG(1, "timeout for register %s", msg.reg[j]->info.name.c_str());

        // orphan any replies for this register
        for(size_t m=0, N=inflight.size(); m<N; m++)
        {
            for(unsigned k=0; k<DevMsg::nreg; k++)
            {
                inflight[m].reg[k] = 0;
            }
        }

        if(!reg_send.empty() && reg_send.front()==reg) {
            // timeout before all sent
            reg_send.pop_front();
        } else {
            assert(reg->next_send>=reg->mem_tx.size());
        }

        reg->state = DevReg::Invalid;

        reg->stat = COMM_ALARM;
        reg->sevr = INVALID_ALARM;
        reg->process(true);

        reg->scan_interested();
    }

    msg.clear();
}

void Device::handle_inspect(Guard &G)
{
    // Process ROM to extract JSON

    ROM rom2, rom16, rom;

    // Try to decode ROM starting at 0x800 and then 0x4000
    rom2.parse((char*)&reg_rom2->mem_rx[0], reg_rom2->mem_rx.size()*4);
    if (rom2.begin() != rom2.end()) {
        rom = rom2;
    } else {
        rom16.parse((char*)&reg_rom16->mem_rx[0], reg_rom16->mem_rx.size()*4);
        rom = rom16;
    }

    std::string json;

    unsigned i=0;
    for(ROM::infos_t::const_iterator it = rom.begin(), end = rom.end();
        it != end; ++it, i++)
    {
        const ROMDescriptor& desc = *it;

        switch(desc.type) {
        case ROMDescriptor::Invalid:
            IFDBG(2, "ROM contains invalid descriptor #%u", i);
            break;
        case ROMDescriptor::Text:
            IFDBG(2, "ROM desc \"%s\"", desc.value.c_str());
            if(description.empty())
                description = desc.value;
            break;
        case ROMDescriptor::BigInt:
            if(jsonhash.empty())
                jsonhash = desc.value;
            else if(codehash.empty())
                codehash = desc.value;
            break; // ignore
        case ROMDescriptor::JSON:
            if(json.empty())
                json = desc.value;
            else
                IFDBG(2, "ROM ignoring addition JSON #%u", i);

            break;
        }
    }

    if(json.empty())
        throw std::runtime_error("ROM contains no JSON");

    JBlob blob;
    blob.parse(json.c_str());

    info32.swap(blob.info32);

    zdeflate(raw_infos, json.c_str(), json.size(), 9);

    // iterate registers and find interested
    for(JBlob::const_iterator it = blob.begin(), end = blob.end(); it != end; ++it)
    {
        const JRegister& reg = it->second;

        if(reg_by_name.find(reg.name)!=reg_by_name.end())
            continue; // don't overwrite automatic/bootstrap register

        IFDBG(2, "add register %s", reg.name.c_str());

        feed::auto_ptr<DevReg> dreg(new DevReg(this, reg));

        // The following isn't directly exception safe (leaves dangling pointers)
        // however, the catch in run() will call reset() which cleans these up

        // fill in list of interested records
        std::pair<reg_interested_t::const_iterator, reg_interested_t::const_iterator> range;
        range = reg_interested.equal_range(reg.name);

        for(; range.first != range.second; ++range.first)
        {
            RegInterest *interest = range.first->second;

            dreg->interested.push_back(interest);

            interest->reg = dreg.get();
        }

        reg_by_name[reg.name] = dreg.release();
    }

    RegInterest::infos_t infos;

    for(reg_interested_t::iterator it(reg_interested.begin()), end(reg_interested.end());
        it != end; ++it)
    {
        const RegInterest * const interest = it->second;

        interest->getInfo(infos);
    }

    // Print driver JSON blob
    std::ostringstream strm;

    strm<<"{"
            "\"peer\": \""<<peer_name<<"\","
            "\"records\": {";

    bool first1 = true;
    for(RegInterest::infos_t::const_iterator it(infos.begin()), end(infos.end()); it!=end; ++it)
    {
        if(!first1) {
            strm<<",";
        } else {
            first1 = false;
        }
        strm<<"\""<<it->first<<"\": {";
        bool first2 = true;
        for(RegInterest::info_items_t::const_iterator it2(it->second.begin()), end2(it->second.end()); it2!=end2; ++it2)
        {
            if(!first2) {
                strm<<",";
            } else {
                first2 = false;
            }
            strm<<"\""<<it2->first<<"\": "<<it2->second;
        }
        strm<<"}";
    }

    strm<<  "}"
          "}";

    std::string jstring(strm.str());

    dev_infos.clear();
    zdeflate(dev_infos, jstring.c_str(), jstring.size(), 9);

    {
        UnGuard U(G);

        for(reg_interested_t::iterator it(reg_interested.begin()), end(reg_interested.end());
            it != end; ++it)
        {
            RegInterest * const interest = it->second;

            if(interest->reg)
                interest->connected(); // allowed to lock record and force post meta-data fields
        }
    }
}

void Device::handle_state(Guard &G)
{
    state_t prev = current;
    if(reset_requested || error_requested) {
        reset(error_requested);
        return;
    }

    switch(current) {
    case Error:
        break; //TODO: Error state latched.  Remove for auto-recover?

    case Idle:
        if(!peer_name.empty()) {
            current = Searching;
            IFDBG(3, "Searching for %s", peer_name.c_str());
        }
        break;

    case Searching:
        if(reg_id->state==DevReg::InSync) {
            // InSync means reply received
            reg_rom2->queue(false);
            reg_rom16->queue(false);
            current = Inspecting;

        }else if(!reg_id->inprogress()) {
            // Timeout.  request again
            reg_id->queue(false);
        }
        break;

    case Inspecting:
        if(reg_rom2->state==DevReg::InSync && reg_rom16->state==DevReg::InSync) {
            handle_inspect(G);
            IFDBG(3, "Request on_connect scan");
            scanIoRequest(on_connect);
            current = Running;
        }
        break;

    case Running:
        break;
    }

    if(prev!=current) {
        IFDBG(3, "Transition %s -> %s", current_name[prev], current_name[current]);
        scanIoRequest(current_changed);
    }
}

void Device::run()
{
    IFDBG(4, "Worker starts");
    Guard G(lock);

    loop_time = epicsTime::getCurrent();

    std::vector<std::vector<char> > bufs(inflight.size());
    // pre-alloc Rx buffers
    for(size_t i=0; i<bufs.size(); i++)
        bufs[i].resize(pkt_size_limit+16);

    // flags for which bufs[i] have been filled
    std::vector<bool> doProcess(inflight.size(), false);

    std::vector<PrintAddr> addrs(inflight.size());

    pollfd fds[2];
    fds[0].fd = sock;
    fds[1].fd = wakeupRx;

    while(!runner_stop) {
        try {
            IFDBG(4, "Looping state=%u", current);

            if(current!=Error && current!=Idle)
                handle_send(G);

            fds[0].events = POLLIN;
            fds[1].events = POLLIN;
            fds[0].revents = fds[1].revents = 0; // paranoia

            if(want_to_send) {
                fds[0].events |= POLLOUT;
            }

            epicsTime after_poll;
            {
                DevReg::records_t completed;
                completed.swap(records);

                UnGuard U(G);

                // Hack.
                // only active if there is a logic error somewhere in async record handling
                if(current == Error && completed.empty() && after_reset) {
                    for(reg_interested_t::iterator it(reg_interested.begin()), end(reg_interested.end());
                                                      it!=end; ++it)
                    {
                        RegInterest *item = it->second;
                        // no-op unless PACT!=0
                        item->complete();
                    }

                    after_reset = false;
                }

                for(DevReg::records_t::const_iterator it = completed.begin(), end = completed.end();
                    it != end; ++it)
                {
                    (*it)->complete();
                }

                std::fill(doProcess.begin(),
                          doProcess.end(),
                          false);

                int ret = ::poll(fds, 2, feedTimeout*1000);

                after_poll = epicsTime::getCurrent();

                if(ret<0) {
                    throw SocketError(SOCKERRNO);

                } else if(ret==0) {
                    // timeout w/o reply

                } else {

                    if(fds[1].revents&(POLLERR|POLLHUP)) {
                        throw std::runtime_error("socket error from wakeupRx");
                    }

                    if(fds[0].revents&POLLERR) {
                        throw std::runtime_error("socket error from serve");
                    }

                    if(fds[1].revents&POLLIN) {
                        fds[1].revents &= ~POLLIN;

                        char temp[16];
                        wakeupRx.recvsome(temp, 16);
                    }

                    if(fds[0].revents&POLLIN) {
                        fds[0].revents &= ~POLLIN;

                        unsigned nrecv=0;
                        for(size_t i=0, N=bufs.size(); i<N; i++)
                        {

                            bufs[i].resize(pkt_size_limit+16);

                            osiSockAddr peer;
                            try{
                                sock.recvfrom(peer, bufs[i]);
                                addrs[i] = peer;
                                doProcess[i] = true;
                                cnt_recv++;
                                cnt_recv_bytes += unsigned(feedUDPHeaderSize) + bufs[i].size();
                            }catch(SocketError& e){
                                if(e.code==SOCK_EWOULDBLOCK) {
                                    break;
                                } else {
                                    throw;
                                }
                            }

                            if(!doProcess[i]) {
                                // nothing to process
                            } else if(!sockAddrAreIdentical(&peer, &peer_addr)) {
                                IFDBG(4, "Warning, RX ignore message from %s", addrs[i].c_str());
                                cnt_ignore++;
                                doProcess[i] = false;

                            } else if(bufs[i].size()>pkt_size_limit+7) {
                                // complain if an extra cmd+addr+data is included
                                IFDBG(0, "Warning, RX message truncated expect=%zu threshold=%zu",
                                      bufs[i].size(), pkt_size_limit+7);
                            }

                            if(doProcess[i])
                                nrecv++;
                        }

                        IFDBG(4, "Received %u messages", nrecv);
                    }
                }

                // re-lock
            }
            loop_time = after_poll;

            if(fds[0].revents&POLLOUT) {
                fds[0].revents &= ~POLLOUT;
                want_to_send = false;
                // loop around and try to send
            }

            if(fds[0].revents || fds[1].revents)
                IFDBG(4, "Unhandled poll() events [0]=%x [1]=%x", fds[0].revents, fds[1].revents);

            for(size_t i=0, N=bufs.size(); i<N; i++)
            {
                if(doProcess[i]) {
                    handle_process(bufs[i], addrs[i]);
                }
            }

            handle_timeout();

            handle_state(G);

        } catch(std::exception& e) {
            cnt_err++;
            reset();
            current = Error;
            errlogPrintf("%s: exception in worker: %s\n", myname.c_str(), e.what());
            last_message = e.what();
            scanIoRequest(current_changed);
        }
    }
    IFDBG(4, "Runner stopping");
}

void Device::show ( unsigned int ) const {}

void Device::show(std::ostream& strm, int lvl) const
{
    Guard G(lock);

    strm<<" Current state: "<<current_name[current]<<"\n"
          " Peer: "<<peer_name<<"\n"
          " Msg: "<<last_message<<"\n"
          " Cnt Tx: "<<cnt_sent<<"\n"
          " Cnt Rx: "<<cnt_recv<<" ("<<cnt_recv_bytes<<" bytes)\n"
          " Cnt Ig: "<<cnt_ignore<<"\n"
          " Cnt TM: "<<cnt_timo<<"\n"
          " Cnt ER: "<<cnt_err<<"\n"
          " Cnt SQ: "<<send_seq<<"\n"
          ;

    if(lvl<=0)
        return;

    strm<<" Messages:\n";
    for(size_t i=0; i<inflight.size(); i++)
    {
        strm<<"  ["<<i<<"] -> ";
        inflight[i].show(strm, lvl);
    }

    if(lvl<=1)
        return;

    strm<<" Send queue:\n";
    for(reg_send_t::const_iterator it(reg_send.begin()), end(reg_send.end());
        it != end; ++it)
    {
        const DevReg *reg = *it;
        strm<<"  "<<reg->info.name<<"\n";
    }

    if(lvl<=2)
        return;

    strm<<" Interests:\n";
    for(reg_interested_t::const_iterator it = reg_interested.begin(), end = reg_interested.end();
        it != end; ++it)
    {
        strm<<"  ";
        it->second->show(strm, lvl);
        strm<<" -> "<<it->first<<"\n";
    }

    if(lvl<=3)
        return;

    strm<<" Registers:\n";

    for(reg_by_name_t::const_iterator it = reg_by_name.begin(), end = reg_by_name.end();
        it != end; ++it)
    {
        strm<<"  "<<it->first;
        it->second->show(strm, lvl);
    }
}


void DevMsg::show(std::ostream& strm, int lvl) const
{
    switch(state) {
    case Free:
        strm<<"Free\n";
        return;
    case Ready:
        strm<<"Ready\n";
        break;
    case Sent:
        strm<<"Sent due=";
    {
        char buf[128];
        due.strftime(buf, sizeof(buf), "%H:%M:%S.%f");
        buf[sizeof(buf)-1] = '\0';
        strm<<buf<<"\n";
    }
        break;
    }
}


void DevReg::show(std::ostream& strm, int lvl) const
{
    if(lvl>=2)
        strm<<" : "<<this->info;

    strm<<"\n"
          "   Reg State: "<<this->state<<"\n"
          "   next_send: "<<this->next_send<<"\n"
          "   Pending async records:\n"
          ;

    for(DevReg::records_t::const_iterator it2 = this->records_inprog.begin(), end2 = this->records_inprog.end();
        it2 != end2; ++it2)
    {
        RegInterest * const reg = *it2;
        strm<<"    ";
        reg->show(strm, lvl);
        strm<<"\n";
    }

    strm<<"  Pending write records:\n";
    for(DevReg::records_t::const_iterator it2 = this->records_write.begin(), end2 = this->records_write.end();
        it2 != end2; ++it2)
    {
        RegInterest * const reg = *it2;
        strm<<"    ";
        reg->show(strm, lvl);
        strm<<"\n";
    }

    strm<<"  Pending read records:\n";
    for(DevReg::records_t::const_iterator it2 = this->records_read.begin(), end2 = this->records_read.end();
        it2 != end2; ++it2)
    {
        RegInterest * const reg = *it2;
        strm<<"    ";
        reg->show(strm, lvl);
        strm<<"\n";
    }

    strm<<"  Interested records:\n";
    for(DevReg::interested_t::const_iterator it2(this->interested.begin()), end2(this->interested.end());
        it2 != end2; ++it2)
    {
        RegInterest *reg(*it2);
        strm<<"    ";
        reg->show(strm, lvl);
        strm<<"\n";
    }
}
