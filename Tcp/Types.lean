/-!
# Core TCP Types

Port, Socket, Segment header, and Transmission Control Block (TCB) structures.

This module defines the fundamental data types used throughout the TCP
formalization: port numbers, socket addresses (IP + port), the segment header
fields specified in RFC 793 Section 3.1, and the TCB variables (SND.UNA,
SND.NXT, SND.WND, RCV.NXT, RCV.WND, ISS, IRS) that track connection state.
-/

namespace Tcp.Types

end Tcp.Types
