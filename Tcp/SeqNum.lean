/-!
# Sequence Number Arithmetic

Modular 32-bit sequence number type and arithmetic operations for TCP.

RFC 793 defines sequence numbers as unsigned 32-bit integers with modular
arithmetic. The comparison relation is meaningful only within a half-space
(2³¹ window), making it a partial rather than total order. This module
defines the `SeqNum` type, wrapping arithmetic, and the "less than" relation
over the circular sequence space.
-/

namespace Tcp.SeqNum

end Tcp.SeqNum
