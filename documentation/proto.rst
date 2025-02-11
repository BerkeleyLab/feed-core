.. role:: raw-latex(raw)
   :format: latex
..

Protocol
========

LBNL Embedded Ethernet Protocol is
A Request/Reply style protocol using UDP on port 50006. A Device
(Server) receives Requests on port 50006 and responds to each valid
Request with a single Reply.

Requests and Replies act on 32-bit registers in a 64MB address space.
The 24-bit Address field acts as the upper bits of a 26-bit address.

UDP Message Format
------------------

.. raw:: html

   <pre>
              0       1         2         3
         +--------+--------+--------+--------+
      00 |              Header...            |
         +--------+--------+--------+--------+
      04 |           ...Header               |
         +--------+--------+--------+--------+
      08 |  Bits  |      Address 1           |
         +--------+--------+--------+--------+
      0C |             Data 1                |
         +--------+--------+--------+--------+
      10 |  Bits  |      Address 2           |
         +--------+--------+--------+--------+
      14 |             Data 2                |
         +--------+--------+--------+--------+
      18 |  Bits  |      Address 3           |
         +--------+--------+--------+--------+
      1C |             Data 3                |
         +--------+--------+--------+--------+
         ...  Repeat Bits/Address/Data
   </pre>

Request and Reply messages have the same format. Each UDP message,
request or reply, is composed of a 8 byte header followed by between 3
and 127 address/data pairs. Total message size *must* be at least 32
bytes. The real maximum limit is the ethernet MTU less transport
protocol headers. For the default 1500 bytes and UDP/IPv4 (42 header
bytes) this is 1456 bytes of UDP payload. Messages size *should* be a
multiple of 8 bytes. Recipients *must* truncate messages to a multiple
of 8 bytes.

Message fields are in Most Significant Byte first (MSB or network) byte
order.

It is *suggested* to pad messages shorter than 32 bytes with reads of
address 0.

Message Fields
--------------

Header
~~~~~~

Echoed without modification from Request to Reply. May be assigned
arbitrarily by a Requester to aid in Reply processing.

Bits
~~~~

This 1 byte field selects the operation in which the Address and Data.

-  0x10 This bit is *set* for a *Read* operation, and
   *cleared* for a *Write*. This bit is echoed in a Reply.

-  0xef The remaining 7 bits are not currently used and should be zeroed
   in Requests and ignored in Replies.

Address
~~~~~~~

This 3 byte (24 bit) address selects 4 bytes in the 64MB device address
space.

For example, address 0 selects bytes 0-3 while address 1 selects bytes
4-7.

MSB order.

Data
~~~~

When Bits[4] is set (Read operation) this field is ignored in Requests
and filled in for Replies.

When Bits[4] is clear (Write operation) this field contains the value to
be written, which is *echoed* in Replies.

To read back the actual value of a register after a write operation, a
Read operation with the same address may be added following a Write
within the same message.

Example message
---------------

Request

.. raw:: html

   <pre>
    00 | 6c656570 89abcdef 
    08 | 01000000 00000000
    10 | 00010000 12345678
    18 | 01010000 00000000
   </pre>

This Request consists of:

-  Arbitrarily chosen Header of 0x6c65657089abcdef
-  A read of address 0 (data ignored)
-  A write of address 0x10000 with data value 0x12345678.
-  A read of address 0x10000 (data ignored)

A corresponding Reply might be:

.. raw:: html

   <pre>
    00 | 6c656570 89abcdef 
    08 | 01000000 48656c6c
    10 | 00010000 12345678
    18 | 01010000 00345678
   </pre>

-  Header echoed from Request
-  Address 0 reads 0x48656c6c
-  A write of address 0x10000 with 0x12345678 is echoed.
-  Address 0x10000 reads 0x00345678 (perhaps due to truncation)

Required Registers
------------------

0x000000 - 0x000003
~~~~~~~~~~~~~~~~~~~

The first 4 registers will read back the 16 byte constant value “Hello
World!:raw-latex:`\r\n`:raw-latex:`\r\n`”.

.. raw:: html

   <pre>
   00 | 48656c6c 6f20576f 726c6421 0d0a0d0a
   </pre>

0x000800 - 0x000fff
~~~~~~~~~~~~~~~~~~~

These 2048 registers access static configuration data. See section
Configuration ROM.

If 0x800 has a zero (0) value, then the altnerate ROM location should be
used.

Alternate ROM location
~~~~~~~~~~~~~~~~~~~~~~

Consists of 16384 registers 0x004000 - 0x007fff containing static
configuration data. See section Configuration ROM.

Configuration ROM Format
------------------------

The register range 0x800 - 0xfff holds static data describing the
device. In each 4 byte register, only the 2 lower bytes are used.

The ROM holds a series of variable length records concatenated together.
Each record begins with a 2 byte Descriptor consisting of a type code in
the upper 2 bits (T), and a 14 bit length (L). The length has units of 4
byte *registers*.

.. raw:: html

   <pre>
              0       1         2         3
         +--------+--------+--------+--------+--------
      00 |    0   |    0   |TTLLLLLL|LLLLLLLL| Data...
         +--------+--------+--------+--------+--------
   </pre>

Type 0
~~~~~~

Indicates the end of the ROM.

Type 1
~~~~~~

The bytes following the Descriptor are an ASCII string.

When multiple Type 1 headers are encountered, they *must* be interpreted
as:

1. Label of firmware

Additional instances may be ignored.

Type 2
~~~~~~

The bytes following the Descriptor are a variable length integer (in
MSB).

A length of 10 (20 bytes valid data) is interpreted as a SHA1 hash.

When multiple Type 2 headers are encountered, they *must* be interpreted
as:

1. A Hash of the JSON text.
2. Git revision of firmware

Additional instances may be ignored.

Type 3
~~~~~~

The bytes following the Descriptor are a zlib compressed (cf. RFC’s
1950, 1951, and 1952) string in the JSON format. This is described in
the JSON Information section.

Example
~~~~~~~

.. raw:: html

   <pre>
    00 | 00004003 00004865 00006c6c 00006f00
    10 | 00000000
   </pre>

Contains:

-  Type 1 Descriptor with length 3 holding the string “Hello\0”.
-  Type 0 Descriptor indicating end of ROM

JSON Information
----------------

The JSON blob encoded in the Configuration ROM will contain a Object
(aka. mapping or dictionary). The keys of this dictionary are symbolic
register names, with the exception of a special name “**metadata**”
which is used to hold device wide information.

The value associated with each register is also an Object containing the
keys:

“access”:“r” \| “w” \| “rw”
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Note whether the register may be read and/or written.

“base_addr”: Number
~~~~~~~~~~~~~~~~~~~

The (first) Address of this register.

“addr_width”: Number
~~~~~~~~~~~~~~~~~~~~

Determines number of Addresses which constitute this register. Number of
Addresses is 2 to the power of addr_width.

::

     naddrs = 1u<<addr_width;

eg. an addr_width of 0 defines a register with exactly one Address.

“data_width”: Number
~~~~~~~~~~~~~~~~~~~~

The number of active data bits. A width of 8 indicates that valid bits
are: 0x000000ff

“sign”: “unsigned” \| “signed”
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Whether values should be interpreted as unsigned or signed (2’s
complement) integers.

“description”: String
~~~~~~~~~~~~~~~~~~~~~

An arbitrary string describing this register.

.. _example-1:

Example
~~~~~~~

::

   {
       "J18_debug": {
           "access": "r",
           "addr_width": 0,
           "base_addr": 63,
           "data_width": 4,
           "sign": "unsigned"
       },
       "__metadata__": {
           "special": "sauce"
       }
   }
