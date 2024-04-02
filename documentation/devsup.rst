Device Support
==============

Overview
--------

The FEED driver for EPICS does not require an explicit instance creation
step. Instead instances are created lazily on first usage. The Device IP
address is set, and may be changed, through a record with
``field(DTYP, "FEED Set Address")``.

See the installed ``feed.dbd`` for the authoritative list of
Device Supports and IOCsh variables.

IOC Shell Variables
-------------------

-  ``int feedNumInFlight`` The number of concurrent requests which will
   be made to any one device. Default 1.
-  ``double feedTimeout`` Timeout in seconds for an individual
   request/reply exchange. Default 1.0
-  ``int feedUDPHeaderSize`` Size in byte of transport layer headers.
   Used only in estimated bandwidth calculations. Default 42.
-  ``int feedUDPPortNum`` The default UDP port number. The default for
   this default is ``50006``.

INP / OUT link format
---------------------

All FEED device supports expect ``INP`` or ``OUT`` to be prefixed by
``@``. aka. ``INST_IO`` followed by a space separated list of
``key=value`` pairs. Only ``name=`` is required by all ``DTYP``. See
below for which keys are understood by which ``DTYP``.

Valid keys are:

-  ``name=`` The Instance name. Must be unique within an IOC process.
-  ``reg=`` Register name. Must match key in Device JSON blob.
-  ``offset=`` Array registers only. Offset of first word accessed.
   Default ``0``.
-  ``step=`` Array registers only. Number of words between accesses.
   Default ``1``.
-  ``scale=`` Multiplier used for ``aai``/``aao`` with ``FTVL`` set to
   ``DOUBLE``. Default ``1.0``.
-  ``wait=`` Boolean. See below.
-  ``rbv=`` Boolean. Input records only. ``false`` (default), use value
   from previous read op. ``true``, use value from previous write
   (combine with ``I/O Intr`` for readback of setting)
-  ``signal=`` “signal” name in IOC JSON blob. Omitted when not set.
-  ``meta=``. Boolean. Update record meta-data fields from Device JSON
   when entering Running state. Default ``false``.
-  ``mask=``, ``value=``, ``retry=``. See Register Watch device support

TPRO Debugging
--------------

FEED Device Supports where ``TPRO > 1`` will log extra information.

Register access
---------------

Each record with a register Read or Write device support will enqueue a
request for a remote read or write operation on all addresses of the
named (by string) register.

Internally, the FEED driver will manage batching of pending requests
into UDP packets.

FEED Register Read
~~~~~~~~~~~~~~~~~~

Supported for record types: longin, ai (RVAL), mbbi (RVAL), and aai.

Asynchronous device support when ``wait=true`` (default), initiate
register read. Synchronous when ``wait=false``, read from local cache.

On scan, request read of the named register. Processing completes on
success, with updated VAL/RVAL, or an ``INVALID`` alarm on timeout.

When ``SCAN`` set to ``I/O Intr``, record will be processed when after
the named register has been read for any reason (eg. some other record)
using the value returned by that operation. Or an ``INVALID`` alarm on
timeout.

For ``aai`` record type. Supported ``FTVL`` are: ``CHAR``, ``UCHAR``,
``SHORT``, ``USHORT``, ``LONG``, ``ULONG``, or ``DOUBLE``. Link options
``offset=`` and/or ``step=`` allow slicing of array registers. When
``FTVL`` is ``DOUBLE``, link option ``scale=`` multiplier is used.

::

   # poll the required HELLO register
   record(longin, "$(PREF)HELLO-I") {
       field(DTYP, "FEED Register Read")
       field(INP , "@name=$(NAME) reg=HELLO")
       field(SCAN, "2 second")
   }
   record(aai, "$(PREF)FW_ROM") {
       field(DTYP, "FEED Register Read")
       field(INP , "@name=$(NAME) reg=ROM")
       field(SCAN, "I/O Intr")
       field(FTVL, "LONG")
       field(NELM, "2048")
   }

FEED Register Write
~~~~~~~~~~~~~~~~~~~

Supported for record types: longout, ao (RVAL), mbbo (RVAL), and aao.

Asynchronous device support when ``wait=true`` (default), wait for
register write operation to complete. Synchronous when ``wait=false``,
initiate write and immediately continue.

On scan, request write of the named register. Processing completes on
success, with updated VAL/RVAL, or an ``INVALID`` alarm on timeout.

When ``FTVL`` is ``DOUBLE``, link option ``scale=`` multiplier is used.

::

   record(longout, "$(BASE)$(N)") {
       field(DTYP, "FEED Register Write")
       field(OUT , "@name=$(NAME) reg=$(REG)")
   }

bo / FEED Register Watch
~~~~~~~~~~~~~~~~~~~~~~~~

Special repeated read operation to poll for bit field register.

Once initiated, polls until success or device timeout.

::

   # wait for value & $(RDY_MASK) == $(RDY_MASK) for reg $(RDY_REG)
   record(bo, "$(BASE)$(N)") {
       field(DTYP, "FEED Register Watch")
       field(OUT , "@name=$(NAME) retry=$(RETRY=0.1) reg=$(RDY_REG) mask=$(RDY_MASK) value=$(RDY_MASK)")
   }


FEED Sync
~~~~~~~~~

The special DTYP="FEED Sync" support exists to allow sequencing during (re)connection.
This asynchronous record will complete processing after every in-progress register read/write
has completed (or timed out). ::

    record(longin, "$(BASE)Init3_") {
        field(DTYP, "FEED Sync")
        field(INP , "@name=$(NAME)")
    }

Signals
-------

The Signals device supports allow some parameters specified in
an INP/OUT link to be changed after initialization via
a different record.

The association between two records is made with the 'signal=' parameter.
Which is a IOC wide unique identifier (unique to one of the  Register Read/Write DTYPs).

Signal names may be selected arbitrarily.
It is suggeste to use a combination of record name prefix,
device name, and/or register name.

In this example, the "$(P)Off-SP" controls, and overrides, the offset=
paramter for "$(P)-I". ::

    record(aai, "$(P)-I") {
        field(DTYP, "FEED Register Read")
        field(INP , "@name=<devicename> reg=<regname> signal=$(P):<regname>")
        ...
    }
    register(longout, "$(P)Off-SP") {
        field(DTYP, "FEED Signal Offset")
        field(OUT , "@signal=$(P):<regname>")
        ...
    }

Currently only the offset, step=, and scale= parameters may be override via the Signals mechanism.

Drive Instance control/status
-----------------------------

See ```feed_base.template`` <src/Db/feed_base.template>`__ for the
recommended starting set of device control and status records.

longout / FEED Debug
~~~~~~~~~~~~~~~~~~~~

Sets the instance debug printing mask.

::

   record(longout, "$(PREF)DEBUG") {
       field(DTYP, "FEED Debug")
       field(OUT , "@name=$(NAME)")
   }

stringout / FEED Force Error
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Force the instance into the latching Error state. The driver will stop
all communication attempts until forced out of the error state by
(re)setting the IP address.

::

   record(stringout, "$(PREF)HALT_") {
       field(DTYP, "FEED Force Error")
       field(OUT , "@name=$(NAME)")
   }

stringout / FEED Set Address
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Set the instance IP address and port.

::

   record(stringout, "$(PREF)IPADDR") {
       field(DTYP, "FEED Set Address")
       field(OUT , "@name=$(NAME)")
   }

mbbi / FEED State
~~~~~~~~~~~~~~~~~

Instance “connection” state.

-  0, ``Error`` Latching error state. No communition attempted until
   reset (by setting IP address)
-  1, ``Idle``. Not latching. Not “connected” and no IP address set.
-  2, ``Searching``. Not “connected”, periodically probing for device
-  3, ``Inspecting``. Reading out and processing ROM image
-  4, ``Running``. Normal operation

::

   record(mbbi, "$(PREF)STATUS") {
       field(DTYP, "FEED State")
       field(INP , "@name=$(NAME)")
   }

longin / FEED On Connect
~~~~~~~~~~~~~~~~~~~~~~~~

Processed on transition into Running state.

::

   record(longin, "$(BASE)$(N)") {
       field(DTYP, "FEED On Connect")
       field(INP , "@name=$(NAME)")
       field(SCAN, "I/O Intr")
   }

aai / FEED Error
~~~~~~~~~~~~~~~~

``FTVL=CHAR`` holds most recent error message string.

::

   record(aai, "$(PREF)LAST_ERROR") {
       field(DTYP, "FEED Error")
       field(INP , "@name=$(NAME)")
       field(SCAN, "I/O Intr")
       field(FTVL, "CHAR")
       field(NELM, "256")
   }

longin / FEED Counter
~~~~~~~~~~~~~~~~~~~~~

Poll diagnostic counter by numeric index.

-  0, UDP packets sent to device
-  1, UDP packets received from device
-  2, UDP packets ignored (eg. malformed)
-  3, Timeouts occurred
-  4, Internal driver errors occurred
-  5, Sequence number of next request
-  6, Bytes received from device, including estimate of transport
   protocol overhead.

::

   record(longin, "$(PREF)$(N)") {
       field(DTYP, "FEED Counter")
       field(INP , "@name=$(NAME) offset=$(INDEX)")
   }

ai / FEED RTT
~~~~~~~~~~~~~

Average round trip time between last 100 requests and replies.

::

   record(ai, "$(PREF)RTT") {
       field(DTYP, "FEED RTT")
       field(INP , "@name=$(NAME)")
   }

aai / FEED JBlob
~~~~~~~~~~~~~~~~

zlib compressed JSON blob. “offset” 0 is the IOC description blob,
“offset” 1 is a copy of most recent Device blob.

::

   record(aai, "$(PREF)JINFO") {
       field(DTYP, "FEED JBlob")
       field(INP , "@name=$(NAME) offset=0")
       field(SCAN, "I/O Intr")
       field(FTVL, "CHAR")
       field(NELM, "16000")
   }
   record(aai, "$(PREF)JSON") {
       field(DTYP, "FEED JBlob")
       field(INP , "@name=$(NAME) offset=1")
       field(SCAN, "I/O Intr")
       field(FTVL, "CHAR")
       field(NELM, "16000")
   }

aai / FEED ROM Info
~~~~~~~~~~~~~~~~~~~

Information by numeric index from Device ROM image.

-  0, Application description string
-  2, Application Git revision hash

::

   record(aai, "$(PREF)$(NAME)") {
       field(DTYP, "FEED ROM Info")
       field(INP , "@name=$(NAME) offset=$(INDEX)")
       field(SCAN, "I/O Intr")
       field(FTVL, "CHAR")
       field(NELM, "256")
   }


longout / FEED Hack lp:1745039
------------------------------

Workaround for bug in epics-base < 7.0.2 when chaining asynchronous
records. A no-op when built with >= 7.0.2

https://bugs.launchpad.net/epics-base/+bug/1745039


dbior
~~~~~

The 'dbior' IOC shell command will give infomation about all FEED Devices.

Simulator Logic
^^^^^^^^^^^^^^^

The simulator can be made to simulator some of the register handling logic
of some devices.  Currently only the RFS waveform acquisition logic is modeled.

The argument -L <name> is used to enable logic handling.
This will fail if the loaded register description doesn't
include all necessary registers.

eg. ::

    ./bin/linux-x86_64/feedsim -L rfs tests/jblob.json

Snapshot and Simulate
---------------------

To snapshot a actual device for simulation, run: ::

    python -m leep.cli <ip> json > capture.json
    python -m leep.cli <ip> dump -Z > capture.initial

This snapshot can then be simulated later: ::

    ./bin/linux-x86_64/feedsim capture.json capture.initial

Protocol
--------

The network protocol implemented by FEED is described in [proto.md](proto.md).
