#ifndef UTILS_H
#define UTILS_H

#include <exception>
#include <sstream>
#include <vector>
#include <memory>

#include <string.h>

#include <osiSock.h>
#include <epicsMutex.h>
#include <epicsGuard.h>
#include <shareLib.h>

#if __cplusplus<201103L
#  define final
#  define override
#endif

typedef epicsGuard<epicsMutex> Guard;
typedef epicsGuardRelease<epicsMutex> UnGuard;


// in-line string builder (eg. for exception messages)
struct SB {
    std::ostringstream strm;
    SB() {}
    operator std::string() const { return strm.str(); }
    template<typename T>
    SB& operator<<(T i) { strm<<i; return *this; }
};

// use std::auto_ptr w/ c++98  (unique_ptr not available).
// use std::unique_ptr w/ c++11 (auto_ptr triggers copious deprecation warnings).
// semantics are the same when used for pImpl
namespace feed {
#if __cplusplus>=201103L
template<typename T>
using auto_ptr = std::unique_ptr<T>;
#define PTRMOVE(AUTO) std::move(AUTO)
#else
using std::auto_ptr;
#define PTRMOVE(AUTO) (AUTO)
#endif
}

// return contents of file
epicsShareExtern std::string read_entire_file(const char *name);

struct epicsShareClass SocketError : public std::exception
{
    const int code;

    SocketError() :code(0) {}
    explicit SocketError(int code) throw() :code(code) {}
    virtual ~SocketError() throw() {}

    const char *what() const throw();
};

// RAII handle to ensure that sockets aren't leaked
// and helper to make socket calls throw SocketError
struct Socket
{
    SOCKET sock;

    Socket() : sock(INVALID_SOCKET) {}

    explicit Socket(SOCKET s);

    Socket(int domain, int type, int protocol);

    ~Socket() {
        close();
    }

    void close() {
        if(sock!=INVALID_SOCKET)
            epicsSocketDestroy(sock);
        sock = INVALID_SOCKET;
    }

    void swap(Socket& o) {
        std::swap(sock, o.sock);
    }

    SOCKET release()
    {
        SOCKET ret = sock;
        sock = INVALID_SOCKET;
        return ret;
    }

    operator SOCKET() const { return sock; }

    void set_blocking(bool block);

    void bind(osiSockAddr& ep) const;

    size_t trysend(const char* buf, size_t buflen) const;

    void sendall(const char* buf, size_t buflen) const;
    size_t recvsome(char* buf, size_t buflen) const;

    void sendto(const osiSockAddr& dest, const char* buf, size_t buflen) const;
    void sendto(const osiSockAddr& dest, const std::vector<char>& buf) const
    { sendto(dest, &buf[0], buf.size()); }

    size_t recvfrom(osiSockAddr& src, char* buf, size_t buflen) const;
    void recvfrom(osiSockAddr& src, std::vector<char>& buf) const
    { buf.resize(recvfrom(src, &buf[0], buf.size())); }

    static void pipe(Socket& rx, Socket& tx);
private:
    Socket(const Socket&);
    Socket& operator=(const Socket&);
};

// lazy printing of socket address
struct PrintAddr
{
    bool init;
    osiSockAddr addr;
    // worst cast size of "<ip>:<port>"
    char buf[4*3 + 3 + 1 + 5 + 1];

    PrintAddr() {clear();}
    explicit PrintAddr(const osiSockAddr& addr)
        :init(false), addr(addr)
    {}
    PrintAddr& operator=(const osiSockAddr& addr) {
        init = false;
        this->addr = addr;
        return *this;
    }
    void clear() {init = true; buf[0]='\0';}
    const char* c_str() {
        if(!init) {
            sockAddrToDottedIP(&addr.sa, buf, sizeof(buf));
            buf[sizeof(buf)-1] = '\0';
            init = true;
        }
        return buf;
    }
};

const char* logTime();

#endif // UTILS_H
