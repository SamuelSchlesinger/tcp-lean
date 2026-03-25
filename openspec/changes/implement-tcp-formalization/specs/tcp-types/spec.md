## ADDED Requirements

### Requirement: Segment Header Structure
The library SHALL define a `Segment` structure containing all TCP header fields
specified in RFC 793 §3.1:
- Source port and destination port (`UInt16`)
- Sequence number and acknowledgment number (`SeqNum`)
- Control bits (`ControlBits` structure with `urg`, `ack`, `psh`, `rst`, `syn`,
  `fin` fields of type `Bool`)
- Window size (`UInt16`)
- Urgent pointer (`UInt16`)
- Segment data (`List UInt8`)

#### Scenario: All header fields accessible
- **WHEN** a `Segment` value is constructed
- **THEN** all RFC 793 §3.1 header fields are individually accessible

### Requirement: Segment Length Computation
The library SHALL define `Segment.len : Segment → UInt32` computing `SEG.LEN`
as the number of octets occupied by the segment in the sequence space: the
length of the data payload, plus 1 if the SYN flag is set, plus 1 if the FIN
flag is set (RFC 793 §3.3: "The segment length (SEG.LEN) includes both data
and sequence space occupying controls").

#### Scenario: SYN-only segment has length 1
- **WHEN** a segment has no data and SYN is set but FIN is not
- **THEN** `Segment.len` returns 1

#### Scenario: Data segment with FIN
- **WHEN** a segment has 100 data octets and FIN is set but SYN is not
- **THEN** `Segment.len` returns 101

### Requirement: Transmission Control Block
The library SHALL define a `Tcb` structure containing all send and receive
sequence variables from RFC 793 §3.2:

**Send variables**: `sndUna` (oldest unacknowledged), `sndNxt` (next to send),
`sndWnd` (send window), `sndUp` (urgent pointer), `sndWl1` (segment seq used
for last window update), `sndWl2` (segment ack used for last window update),
`iss` (initial send sequence number).

**Receive variables**: `rcvNxt` (next expected), `rcvWnd` (receive window),
`rcvUp` (urgent pointer), `irs` (initial receive sequence number).

All sequence-number-valued fields SHALL use the `SeqNum` type. Window fields
SHALL use `UInt16` (matching the 16-bit window field in the header).

#### Scenario: TCB tracks all RFC 793 §3.2 variables
- **WHEN** a `Tcb` value is inspected
- **THEN** every send/receive variable listed in RFC 793 §3.2 is present

### Requirement: TCP State Enumeration
The library SHALL define a `TcpState` inductive type with exactly the 11
connection states from RFC 793 §3.2 plus the fictional CLOSED state:
`Closed`, `Listen`, `SynSent`, `SynReceived`, `Established`, `FinWait1`,
`FinWait2`, `CloseWait`, `Closing`, `LastAck`, `TimeWait`.

#### Scenario: Exhaustive match
- **WHEN** a match expression covers all `TcpState` constructors
- **THEN** Lean confirms the match is exhaustive with exactly 11 cases

### Requirement: User Call Types
The library SHALL define a `UserCall` inductive type representing the six user
commands from RFC 793 §3.8: `Open` (with active/passive mode and optional
foreign socket), `Send` (with data buffer and push/urgent flags), `Receive`,
`Close`, `Abort`, `Status`.

#### Scenario: Active vs passive OPEN distinguished
- **WHEN** a `UserCall.Open` is constructed
- **THEN** it carries an `OpenMode` parameter distinguishing active from passive

### Requirement: Timeout Types
The library SHALL define a `TimeoutKind` inductive type with three constructors
matching RFC 793 §3.9: `UserTimeout`, `Retransmission`, `TimeWait`.

#### Scenario: All three timeout kinds representable
- **WHEN** a timeout event occurs
- **THEN** it can be classified as exactly one of the three `TimeoutKind` values
