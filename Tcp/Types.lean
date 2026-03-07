import Tcp.SeqNum

/-!
# Core TCP Types

Port, Socket, Segment header, and Transmission Control Block (TCB) structures.

This module defines the fundamental data types used throughout the TCP
formalization: port numbers, socket addresses, the segment header fields
specified in RFC 793 §3.1, and the TCB variables (SND.UNA, SND.NXT, SND.WND,
RCV.NXT, RCV.WND, ISS, IRS, etc.) that track connection state per RFC 793 §3.2.
-/

namespace Tcp

-- ============================================================================
-- Port and Socket Address
-- ============================================================================

/-- A TCP port number (16-bit). RFC 793 §2.7. -/
abbrev Port := UInt16

/-- A socket address. We abstract the IP address as a `Nat` since IP-layer
    details are out of scope. RFC 793 §2.7: "a pair of sockets uniquely
    identifies each connection." -/
structure SocketAddr where
  addr : Nat
  port : Port
deriving DecidableEq, Repr

-- ============================================================================
-- Segment Header — RFC 793 §3.1
-- ============================================================================

/-- Control bits in the TCP header. RFC 793 §3.1:
    URG, ACK, PSH, RST, SYN, FIN (6 bits). -/
structure ControlBits where
  urg : Bool := false
  ack : Bool := false
  psh : Bool := false
  rst : Bool := false
  syn : Bool := false
  fin : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- A TCP segment (header + data). Models the relevant fields from
    RFC 793 §3.1. Wire-format fields (checksum, data offset, reserved bits,
    options, padding) are omitted — they concern encoding, not protocol logic.

    RFC 793 §3.1: "TCP Header Format"
    - Source Port (16 bits)
    - Destination Port (16 bits)
    - Sequence Number (32 bits)
    - Acknowledgment Number (32 bits)
    - Control Bits (6 bits: URG, ACK, PSH, RST, SYN, FIN)
    - Window (16 bits)
    - Urgent Pointer (16 bits)
    - Data -/
structure Segment where
  srcPort : Port
  dstPort : Port
  seq     : SeqNum
  ackNum  : SeqNum
  ctl     : ControlBits := {}
  window  : UInt16
  urgPtr  : UInt16 := 0
  data    : List UInt8 := []
deriving Repr

instance : Inhabited Segment where
  default := { srcPort := 0, dstPort := 0, seq := ⟨0⟩, ackNum := ⟨0⟩, window := 0 }

namespace Segment

/-- Segment length including SYN and FIN contributions to sequence space.
    RFC 793 §3.3: "SEG.LEN = the number of octets occupied by the data in
    the segment (counting SYN and FIN)."

    SYN and FIN each occupy one sequence number. -/
def len (seg : Segment) : UInt32 :=
  let dataLen : UInt32 := seg.data.length.toUInt32
  let synLen  : UInt32 := if seg.ctl.syn then 1 else 0
  let finLen  : UInt32 := if seg.ctl.fin then 1 else 0
  dataLen + synLen + finLen

end Segment

-- ============================================================================
-- TCP State — RFC 793 §3.2
-- ============================================================================

/-- The eleven TCP connection states plus CLOSED.
    RFC 793 §3.2, Figure 6 (TCP Connection State Diagram). -/
inductive TcpState where
  | Closed
  | Listen
  | SynSent
  | SynReceived
  | Established
  | FinWait1
  | FinWait2
  | CloseWait
  | Closing
  | LastAck
  | TimeWait
deriving DecidableEq, Repr

-- ============================================================================
-- Transmission Control Block (TCB) — RFC 793 §3.2
-- ============================================================================

/-- The Transmission Control Block stores the per-connection variables.
    RFC 793 §3.2: "Among the variables stored in the TCB are the local and
    remote socket numbers, the security and precedence of the connection,
    pointers to the user's send and receive buffers, pointers to the
    retransmit queue..."

    We model the sequence-number and window variables. Security/precedence
    are omitted per design decision D9. Buffers and queues live on
    `TcpEndpoint` (see `Tcp/State.lean`). -/
structure Tcb where
  /-- Oldest unacknowledged sequence number. RFC 793 §3.2: SND.UNA -/
  sndUna : SeqNum
  /-- Next sequence number to send. RFC 793 §3.2: SND.NXT -/
  sndNxt : SeqNum
  /-- Send window size. RFC 793 §3.2: SND.WND -/
  sndWnd : UInt16
  /-- Send urgent pointer. RFC 793 §3.2: SND.UP -/
  sndUp  : SeqNum
  /-- Segment sequence number used for last window update. RFC 793 §3.2: SND.WL1 -/
  sndWl1 : SeqNum
  /-- Segment ack number used for last window update. RFC 793 §3.2: SND.WL2 -/
  sndWl2 : SeqNum
  /-- Initial send sequence number. RFC 793 §3.2: ISS -/
  iss    : SeqNum
  /-- Next sequence number expected on incoming segments. RFC 793 §3.2: RCV.NXT -/
  rcvNxt : SeqNum
  /-- Receive window size. RFC 793 §3.2: RCV.WND -/
  rcvWnd : UInt16
  /-- Receive urgent pointer. RFC 793 §3.2: RCV.UP -/
  rcvUp  : SeqNum
  /-- Initial receive sequence number. RFC 793 §3.2: IRS -/
  irs    : SeqNum
deriving Repr

-- ============================================================================
-- User Interface Types — RFC 793 §3.8
-- ============================================================================

/-- Whether an OPEN call is active (initiate connection) or passive (listen).
    RFC 793 §3.8: "The OPEN call specifies whether connection establishment
    is to be actively pursued, or to be passively waited for." -/
inductive OpenMode where
  | Active
  | Passive
deriving DecidableEq, Repr

/-- User calls to TCP. RFC 793 §3.8 defines the user/TCP interface:
    OPEN, SEND, RECEIVE, CLOSE, ABORT, STATUS. -/
inductive UserCall where
  /-- OPEN: establish connection. RFC 793 §3.8 -/
  | Open (mode : OpenMode) (iss : SeqNum)
  /-- SEND: enqueue data for transmission. RFC 793 §3.8 -/
  | Send (data : List UInt8)
  /-- RECEIVE: request delivery of received data. RFC 793 §3.8 -/
  | Receive
  /-- CLOSE: initiate graceful close. RFC 793 §3.8 -/
  | Close
  /-- ABORT: destroy connection immediately. RFC 793 §3.8 -/
  | Abort
  /-- STATUS: query connection state. RFC 793 §3.8 -/
  | Status
deriving Repr

/-- Timeout event types. RFC 793 §3.9 specifies three timeout-driven
    behaviors. -/
inductive TimeoutKind where
  /-- User timeout: the connection has been idle too long. -/
  | UserTimeout
  /-- Retransmission timeout: resend unacknowledged data. -/
  | Retransmission
  /-- TIME-WAIT timeout: 2×MSL has elapsed. -/
  | TimeWait
deriving DecidableEq, Repr

/-- Responses returned to the user from TCP calls. -/
inductive UserResponse where
  /-- Success. -/
  | Ok
  /-- Error with a description. -/
  | Error (msg : String)
  /-- Data delivered to user (from RECEIVE). -/
  | Data (bytes : List UInt8)
  /-- Connection state info (from STATUS). -/
  | StateInfo (state : TcpState)
deriving Repr

end Tcp
