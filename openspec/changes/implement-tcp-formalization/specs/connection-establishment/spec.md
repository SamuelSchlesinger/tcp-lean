## ADDED Requirements

### Requirement: Normal Three-Way Handshake Correctness
The library SHALL prove that starting from a `System` where endpoint A is
CLOSED and endpoint B is in LISTEN, if A performs an active OPEN and segments
are delivered reliably, then the system reaches a state where both endpoints
are ESTABLISHED with synchronized sequence numbers:
- `A.tcb.irs = B.tcb.iss` and `B.tcb.irs = A.tcb.iss`
- `A.tcb.sndNxt = A.tcb.iss + 1` and `B.tcb.sndNxt = B.tcb.iss + 1`

This corresponds to RFC 793 §3.4 Figure 7.

#### Scenario: Both endpoints reach ESTABLISHED
- **WHEN** A does active OPEN, SYN is delivered to B, SYN-ACK is delivered to A, ACK is delivered to B
- **THEN** `A.state = Established` and `B.state = Established`

#### Scenario: Sequence numbers synchronized
- **WHEN** the three-way handshake completes
- **THEN** each endpoint's `irs` equals the other's `iss`

### Requirement: Simultaneous Open Correctness
The library SHALL prove that starting from a `System` where both endpoints are
CLOSED, if both perform active OPEN (each sending SYN), then the system reaches
a state where both are ESTABLISHED. Both transition through
CLOSED → SYN-SENT → SYN-RECEIVED → ESTABLISHED.

This corresponds to RFC 793 §3.4 Figure 8.

#### Scenario: Simultaneous SYNs resolve to ESTABLISHED
- **WHEN** both endpoints send SYN, each receives the other's SYN and sends SYN-ACK, each receives SYN-ACK
- **THEN** both endpoints reach ESTABLISHED

### Requirement: Old Duplicate SYN Recovery
The library SHALL prove that an old duplicate SYN arriving at a LISTEN endpoint
is correctly handled: the LISTEN endpoint sends SYN-ACK, the active endpoint
detects the wrong ACK number, sends RST, the LISTEN endpoint returns to LISTEN,
and when the correct SYN arrives the handshake proceeds normally.

This corresponds to RFC 793 §3.4 Figure 9.

#### Scenario: RST rejects stale SYN-ACK
- **WHEN** an old duplicate SYN causes a SYN-ACK with incorrect `SEG.ACK`
- **THEN** the active endpoint sends RST, the passive endpoint returns to LISTEN
- **THEN** the correct SYN subsequently completes the handshake

### Requirement: Half-Open Connection Detection
The library SHALL prove that if one endpoint crashes (state becomes CLOSED) while
the other remains ESTABLISHED, then when the crashed endpoint attempts to
re-open the connection:
- The stale ESTABLISHED endpoint sends an ACK with old sequence numbers
- The reopening endpoint sends RST (sequence number does not match)
- The stale endpoint aborts and enters CLOSED
- The reopening endpoint can then establish a new connection normally

This corresponds to RFC 793 §3.4 Figures 10--11.

#### Scenario: Stale endpoint is reset
- **WHEN** endpoint A crashes and sends new SYN, endpoint B (ESTABLISHED) sends stale ACK
- **THEN** A sends RST, B aborts to CLOSED

### Requirement: Data Piggybacked on SYN
The library SHALL model that SYN segments may carry payload data (RFC 793 §3.4:
"connection synchronization using data-carrying segments... is perfectly
legitimate"). When a data-bearing SYN arrives, the data SHALL be buffered (in
the reassembly buffer or a pending-data queue) and NOT delivered to the user
until the connection reaches ESTABLISHED. The handshake proof SHALL demonstrate
that this buffered data is eventually delivered after synchronization completes.

#### Scenario: Data on SYN buffered until ESTABLISHED
- **WHEN** a SYN segment carrying 100 bytes of data arrives at a LISTEN endpoint
- **THEN** the data is queued during SYN-RECEIVED and delivered only after the endpoint reaches ESTABLISHED

### Requirement: SYN-SENT "Continue Processing" Semantics
The library SHALL correctly model the control flow jump in RFC 793 §3.9
SYN-SENT fourth check: when a SYN-ACK arrives and the endpoint transitions to
ESTABLISHED, if the segment contains additional data or controls, processing
SHALL continue at the sixth step (URG check), skipping steps 1-5 for the
remainder of the segment. This enables piggybacked data on SYN-ACK to be
processed immediately.

#### Scenario: SYN-ACK with data processed through steps 6-8
- **WHEN** a SYN-ACK with payload data arrives in SYN-SENT
- **THEN** after transitioning to ESTABLISHED, the data is processed via the URG/text/FIN checks (steps 6-8)

### Requirement: SYN Occupies Sequence Space
The library SHALL prove that SYN consumes one sequence number: after sending a
SYN segment, `SND.NXT = ISS + 1` (RFC 793 §3.3: "the SYN is considered to
occur before the first actual data octet").

#### Scenario: SND.NXT after SYN
- **WHEN** an active OPEN causes a SYN to be sent
- **THEN** `SND.NXT = ISS + 1`
