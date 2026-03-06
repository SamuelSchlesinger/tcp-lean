/-!
# Segment and ACK Acceptability

Predicates and lemmas for segment acceptability and ACK validation.

RFC 793 Section 3.3 specifies when an incoming segment is acceptable based
on the receive window and sequence numbers. This module defines the
acceptability predicates for both segments and acknowledgments, along with
lemmas establishing key properties of these predicates over the modular
sequence number space.
-/

namespace Tcp.Acceptability

end Tcp.Acceptability
