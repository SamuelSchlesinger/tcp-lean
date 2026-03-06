/-!
# TCP Connection State Machine

TCP connection state enumeration, event types, and the transition function.

RFC 793 Section 3.2 defines eleven connection states (CLOSED, LISTEN,
SYN-SENT, SYN-RECEIVED, ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT,
CLOSING, LAST-ACK, TIME-WAIT). This module formalizes the state enum, the
events that drive transitions (segment arrival, user calls, timeouts), and
the transition function that maps (state, event) pairs to new states.
-/

namespace Tcp.State

end Tcp.State
