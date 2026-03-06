/-!
# Safety and Data Delivery Invariants

Proofs of global safety properties and data delivery guarantees.

This module establishes the overarching correctness properties of the TCP
formalization: safety invariants that hold across all reachable states
(e.g., sequence number consistency, window validity) and liveness/delivery
properties (e.g., data sent is eventually received in order by the
application layer, assuming fair scheduling and bounded network delay).
-/

namespace Tcp.Invariants

end Tcp.Invariants
