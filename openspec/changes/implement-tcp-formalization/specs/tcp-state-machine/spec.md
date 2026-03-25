## ADDED Requirements

### Requirement: TCP Endpoint Structure
The library SHALL define a `TcpEndpoint` structure representing a single TCP
endpoint's complete state, containing:
- `state : TcpState` — current connection state (RFC 793 §3.2)
- `tcb : Tcb` — transmission control block variables
- `openMode : Option OpenMode` — whether connection originated from active or
  passive OPEN (needed for RST handling in SYN-RECEIVED, RFC 793 §3.9)
- `sendQueue : List UInt8` — data queued for transmission
- `recvBuffer : List UInt8` — in-order received data awaiting user RECEIVE
- `reassemblyBuf : List Segment` — out-of-order segments held for reassembly
  (RFC 793 §3.9: "Segments with higher beginning sequence numbers may be held
  for later processing")
- `retxQueue : List Segment` — unacknowledged segments for retransmission
- `finSent : Bool` — whether a FIN has been sent

#### Scenario: Endpoint tracks origin mode
- **WHEN** an endpoint enters SYN-RECEIVED from LISTEN (passive) vs SYN-SENT (active)
- **THEN** `openMode` distinguishes the two cases for RST processing

### Requirement: Two-Endpoint System Model
The library SHALL define a `System` structure modeling two communicating TCP
endpoints and the network between them:
- `endpointA : TcpEndpoint`
- `endpointB : TcpEndpoint`
- `network : List Segment` — in-flight segments (treated as an unordered
  multiset; any element may be delivered next)

The library SHALL define a `SystemStep` inductive type representing one atomic
transition of the system. Steps SHALL include:
- Delivering a segment from `network` to either endpoint
- A user call on either endpoint
- A timeout event on either endpoint
- Segment loss (removing a segment from the network)
- Segment duplication (copying a segment in the network)

#### Scenario: Network reordering
- **WHEN** two segments are in the network
- **THEN** either may be delivered first (both orderings are valid `SystemStep`s)

#### Scenario: Segment loss modeled
- **WHEN** a segment is in the network
- **THEN** a `SystemStep` exists that removes it without delivery

### Requirement: OPEN Call Processing
The event processing function SHALL implement RFC 793 §3.9 OPEN Call behavior
for every state:
- CLOSED + passive → create TCB, enter LISTEN
- CLOSED + active → create TCB, select ISS, send SYN, set `SND.UNA=ISS`,
  `SND.NXT=ISS+1`, enter SYN-SENT
- LISTEN + active → select ISS, send SYN, enter SYN-SENT
- All other states → error (connection already exists)

#### Scenario: Passive OPEN from CLOSED
- **WHEN** a passive OPEN is processed in CLOSED state
- **THEN** the endpoint transitions to LISTEN with a fresh TCB

#### Scenario: Active OPEN from CLOSED
- **WHEN** an active OPEN is processed in CLOSED state
- **THEN** the endpoint transitions to SYN-SENT and emits a SYN segment

### Requirement: SEND Call Processing
The event processing function SHALL implement RFC 793 §3.9 SEND Call behavior:
- CLOSED → error
- LISTEN → switch to active, send SYN, enter SYN-SENT, queue data
- SYN-SENT, SYN-RECEIVED → queue data for after ESTABLISHED
- ESTABLISHED, CLOSE-WAIT → segmentize buffer, send with piggybacked ACK
- FIN-WAIT-*, CLOSING, LAST-ACK, TIME-WAIT → error (connection closing)

#### Scenario: Data queued in SYN-SENT
- **WHEN** a SEND call occurs in SYN-SENT state
- **THEN** data is queued and will be transmitted after reaching ESTABLISHED

#### Scenario: Data segmentized in ESTABLISHED
- **WHEN** a SEND call occurs in ESTABLISHED state
- **THEN** data is packaged into segments and sent with `ACK=RCV.NXT`

### Requirement: RECEIVE Call Processing
The event processing function SHALL implement RFC 793 §3.9 RECEIVE Call
behavior:
- CLOSED → error
- LISTEN, SYN-SENT, SYN-RECEIVED → queue for after ESTABLISHED
- ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2 → deliver buffered data or queue request
- CLOSE-WAIT → deliver remaining data or error if none
- CLOSING, LAST-ACK, TIME-WAIT → error (connection closing)

#### Scenario: Data delivered in ESTABLISHED
- **WHEN** a RECEIVE call occurs in ESTABLISHED and the receive buffer has data
- **THEN** data is returned to the user

### Requirement: CLOSE Call Processing
The event processing function SHALL implement RFC 793 §3.9 CLOSE Call behavior:
- CLOSED → error
- LISTEN → delete TCB, enter CLOSED
- SYN-SENT → delete TCB, enter CLOSED
- SYN-RECEIVED → queue FIN or send FIN, enter FIN-WAIT-1
- ESTABLISHED → send FIN after pending SENDs, enter FIN-WAIT-1
- FIN-WAIT-1, FIN-WAIT-2 → error (already closing)
- CLOSE-WAIT → send FIN after pending SENDs, enter LAST-ACK
- CLOSING, LAST-ACK, TIME-WAIT → error

#### Scenario: CLOSE from ESTABLISHED sends FIN
- **WHEN** CLOSE is called in ESTABLISHED state
- **THEN** a FIN segment is emitted and state transitions to FIN-WAIT-1

### Requirement: ABORT Call Processing
The event processing function SHALL implement RFC 793 §3.9 ABORT Call behavior:
- CLOSED → error
- LISTEN, SYN-SENT → delete TCB, enter CLOSED
- SYN-RECEIVED, ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT → send RST
  (`SEQ=SND.NXT`), flush queues, enter CLOSED
- CLOSING, LAST-ACK, TIME-WAIT → delete TCB, enter CLOSED

#### Scenario: ABORT from ESTABLISHED sends RST
- **WHEN** ABORT is called in ESTABLISHED state
- **THEN** a RST segment with `SEQ=SND.NXT` is emitted and state becomes CLOSED

### Requirement: SEGMENT ARRIVES — CLOSED State
The event processing function SHALL implement RFC 793 §3.9 SEGMENT ARRIVES for
CLOSED state: discard data; if RST, discard; otherwise send RST (if ACK:
`SEQ=SEG.ACK, CTL=RST`; if no ACK: `SEQ=0, ACK=SEG.SEQ+SEG.LEN, CTL=RST,ACK`).

#### Scenario: Non-RST segment to CLOSED generates RST
- **WHEN** a SYN segment arrives at an endpoint in CLOSED state
- **THEN** a RST segment is emitted in response

### Requirement: SEGMENT ARRIVES — LISTEN State
The event processing function SHALL implement RFC 793 §3.9 SEGMENT ARRIVES for
LISTEN state, checking in order: (1) RST → ignore, (2) ACK → send RST,
(3) SYN → set `RCV.NXT=SEG.SEQ+1`, `IRS=SEG.SEQ`, select ISS, send SYN-ACK,
set `SND.NXT=ISS+1`, `SND.UNA=ISS`, enter SYN-RECEIVED, (4) other → drop.

#### Scenario: SYN in LISTEN initiates handshake
- **WHEN** a SYN segment arrives at an endpoint in LISTEN state
- **THEN** the endpoint sends SYN-ACK and transitions to SYN-RECEIVED

### Requirement: SEGMENT ARRIVES — SYN-SENT State
The event processing function SHALL implement RFC 793 §3.9 SEGMENT ARRIVES for
SYN-SENT state with the five-step pipeline: (1) ACK check — reject if
`SEG.ACK ≤ ISS` or `SEG.ACK > SND.NXT`, (2) RST check — if ACK was
acceptable, abort; otherwise drop, (3) security (skip), (4) SYN check — set
`RCV.NXT=SEG.SEQ+1`, `IRS=SEG.SEQ`, advance `SND.UNA`; if our SYN ACKed
(`SND.UNA > ISS`) → ESTABLISHED; else → SYN-RECEIVED, (5) no SYN or RST → drop.

#### Scenario: SYN-ACK in SYN-SENT completes handshake
- **WHEN** a SYN-ACK segment with acceptable ACK arrives at SYN-SENT
- **THEN** the endpoint transitions to ESTABLISHED and sends ACK

#### Scenario: SYN without ACK in SYN-SENT (simultaneous open)
- **WHEN** a SYN segment without ACK arrives at SYN-SENT
- **THEN** the endpoint transitions to SYN-RECEIVED and sends SYN-ACK

### Requirement: SEGMENT ARRIVES — Otherwise (8-check pipeline)
The event processing function SHALL implement RFC 793 §3.9 SEGMENT ARRIVES for
states SYN-RECEIVED, ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT, CLOSING,
LAST-ACK, TIME-WAIT with the following checks **in order**:

1. **Sequence check** (RFC 793 §3.3 acceptability table) — if not acceptable,
   send ACK (unless RST set) and drop
2. **RST check** — SYN-RECEIVED: return to LISTEN (passive) or CLOSED (active);
   ESTABLISHED/FIN-WAIT-*/CLOSE-WAIT: abort, CLOSED;
   CLOSING/LAST-ACK/TIME-WAIT: CLOSED
3. **Security check** — skipped (always passes per design decision D9)
4. **SYN check** — if SYN in window, send RST, abort, CLOSED
5. **ACK check** — must have ACK bit; SYN-RECEIVED: if acceptable ACK →
   ESTABLISHED; ESTABLISHED: advance `SND.UNA`, remove acked retx segments,
   window update; FIN-WAIT-1: if FIN acked → FIN-WAIT-2; CLOSING: if FIN
   acked → TIME-WAIT; LAST-ACK: if FIN acked → CLOSED; TIME-WAIT: ACK
   retransmitted FIN, restart timer
6. **URG check** — update `RCV.UP`, signal user if urgent pointer advances
7. **Segment text** — in ESTABLISHED/FIN-WAIT-1/FIN-WAIT-2: deliver data to
   receive buffer, advance `RCV.NXT`, send ACK; other states: ignore
8. **FIN check** — advance `RCV.NXT`, send ACK; SYN-RECEIVED/ESTABLISHED →
   CLOSE-WAIT; FIN-WAIT-1 → TIME-WAIT (if FIN acked) or CLOSING; FIN-WAIT-2 →
   TIME-WAIT; CLOSE-WAIT/CLOSING/LAST-ACK/TIME-WAIT → remain, restart timer
   if TIME-WAIT

#### Scenario: ACK in SYN-RECEIVED promotes to ESTABLISHED
- **WHEN** an acceptable ACK arrives in SYN-RECEIVED
- **THEN** the endpoint transitions to ESTABLISHED

#### Scenario: Window update in ESTABLISHED
- **WHEN** an ACK arrives in ESTABLISHED with `SND.WL1 < SEG.SEQ`
- **THEN** `SND.WND` is updated to `SEG.WND`

#### Scenario: FIN in ESTABLISHED transitions to CLOSE-WAIT
- **WHEN** a FIN segment arrives in ESTABLISHED
- **THEN** `RCV.NXT` advances past the FIN and state becomes CLOSE-WAIT

#### Scenario: FIN-ACK in FIN-WAIT-1 transitions to TIME-WAIT
- **WHEN** a segment with both ACK (acknowledging our FIN) and FIN arrives in FIN-WAIT-1
- **THEN** the endpoint transitions to TIME-WAIT

### Requirement: Timeout Processing
The event processing function SHALL implement RFC 793 §3.9 timeout behavior:
- **USER TIMEOUT**: flush queues, signal error, enter CLOSED (all states)
- **RETRANSMISSION TIMEOUT**: resend head of retransmission queue, reinitialize
  timer (all states)
- **TIME-WAIT TIMEOUT**: delete TCB, enter CLOSED

#### Scenario: TIME-WAIT timeout closes connection
- **WHEN** the TIME-WAIT timeout fires
- **THEN** the endpoint transitions to CLOSED
