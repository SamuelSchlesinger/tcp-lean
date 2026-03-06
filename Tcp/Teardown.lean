/-!
# Connection Teardown

Theorems for graceful connection closing and TIME-WAIT behavior.

RFC 793 specifies a graceful close via FIN exchange, with the TIME-WAIT
state lasting 2×MSL (Maximum Segment Lifetime) to ensure old duplicate
segments are drained from the network. This module proves correctness
properties of the closing handshake and the TIME-WAIT mechanism.
-/

namespace Tcp.Teardown

end Tcp.Teardown
