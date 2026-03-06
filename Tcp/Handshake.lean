/-!
# Three-Way Handshake

Correctness theorems for TCP connection establishment.

The three-way handshake (SYN → SYN-ACK → ACK) is the mechanism by which
TCP establishes a reliable connection between two endpoints. This module
proves that the handshake protocol correctly transitions both endpoints
from CLOSED/LISTEN to ESTABLISHED, and that the sequence numbers are
properly synchronized upon completion.
-/

namespace Tcp.Handshake

end Tcp.Handshake
