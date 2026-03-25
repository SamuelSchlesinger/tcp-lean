## ADDED Requirements

### Requirement: Normal Close Correctness
The library SHALL prove that when endpoint A issues CLOSE from ESTABLISHED while
B remains in ESTABLISHED, and segments are delivered reliably, then:
- A transitions: ESTABLISHED → FIN-WAIT-1 → FIN-WAIT-2 → TIME-WAIT → CLOSED
- B transitions: ESTABLISHED → CLOSE-WAIT → (user issues CLOSE) → LAST-ACK → CLOSED

Note: RFC 793 §3.9 CLOSE Call for CLOSE-WAIT says "enter CLOSING state" but
this contradicts the state diagram (Figure 6) which shows CLOSE-WAIT → LAST-ACK.
The state diagram is authoritative; CLOSE from CLOSE-WAIT enters LAST-ACK.

This corresponds to RFC 793 §3.5 Figure 13.

#### Scenario: Initiator reaches TIME-WAIT
- **WHEN** A issues CLOSE, sends FIN, B ACKs the FIN
- **THEN** A reaches FIN-WAIT-2

#### Scenario: Responder closes
- **WHEN** B receives FIN, enters CLOSE-WAIT, then user issues CLOSE
- **THEN** B sends FIN, enters LAST-ACK, and when ACK arrives, enters CLOSED

#### Scenario: Initiator completes
- **WHEN** A (in FIN-WAIT-2) receives B's FIN
- **THEN** A enters TIME-WAIT, ACKs the FIN, and after 2×MSL timeout enters CLOSED

### Requirement: Simultaneous Close Correctness
The library SHALL prove that when both endpoints issue CLOSE from ESTABLISHED
simultaneously, both transition through:
FIN-WAIT-1 → CLOSING → TIME-WAIT → CLOSED

This corresponds to RFC 793 §3.5 Figure 14.

#### Scenario: Both endpoints reach TIME-WAIT
- **WHEN** both send FIN simultaneously, each receives the other's FIN while in FIN-WAIT-1
- **THEN** both enter CLOSING, exchange ACKs, and both enter TIME-WAIT

### Requirement: Data Reception During Teardown
The library SHALL prove that data can still be received and delivered to the
user in FIN-WAIT-1 and FIN-WAIT-2 states. RFC 793 §3.5: "The user who CLOSEs
may continue to RECEIVE until he is told that the other side has CLOSED also."
RFC 793 §3.9 seventh check processes segment text in ESTABLISHED, FIN-WAIT-1,
and FIN-WAIT-2.

The FIN sent by the closing side only means "I have no more data to send" — it
does not prevent receiving data from the remote.

#### Scenario: Data arrives in FIN-WAIT-1
- **WHEN** A has sent FIN (in FIN-WAIT-1) and B sends data (B is still ESTABLISHED)
- **THEN** A accepts the data, advances `RCV.NXT`, and delivers it to the user

#### Scenario: Data arrives in FIN-WAIT-2
- **WHEN** A is in FIN-WAIT-2 and B sends data before closing
- **THEN** A accepts and delivers the data normally

### Requirement: FIN With Data
The library SHALL model that a FIN segment may carry payload data (RFC 793 §3.3:
FIN is considered to occur after the last data octet). When a FIN-bearing
segment contains data, the data SHALL be processed first (step 7, segment text),
then the FIN is processed (step 8). FIN implies PUSH for any segment text not
yet delivered (RFC 793 §3.9 eighth check: "FIN implies PUSH for any segment
text not yet delivered to the user").

#### Scenario: FIN segment with data
- **WHEN** a segment with both data and FIN arrives in ESTABLISHED
- **THEN** the data is delivered (with implicit PUSH), `RCV.NXT` advances past both data and FIN, and state transitions to CLOSE-WAIT

### Requirement: FIN Acknowledgment Detection
The library SHALL define how "our FIN is now acknowledged" is determined
(RFC 793 §3.9 fifth check, FIN-WAIT-1 and CLOSING). The FIN occupies the
sequence number `SND.NXT - 1` at the time it was sent (or equivalently, the
FIN's sequence number is tracked in the endpoint). The FIN is acknowledged when
`SEG.ACK > finSeqNum`, where `finSeqNum` is the sequence number assigned to the
FIN.

#### Scenario: FIN acknowledged in FIN-WAIT-1
- **WHEN** a segment arrives in FIN-WAIT-1 with `SEG.ACK` acknowledging the FIN's sequence number
- **THEN** "our FIN is now acknowledged" and the endpoint transitions to FIN-WAIT-2

### Requirement: FIN Occupies Sequence Space
The library SHALL prove that FIN consumes one sequence number: when FIN is sent,
`SND.NXT` advances by 1 beyond the last data octet (RFC 793 §3.3: "the FIN is
considered to occur after the last actual data octet").

#### Scenario: SND.NXT after FIN
- **WHEN** a FIN segment is sent from ESTABLISHED
- **THEN** `SND.NXT` has advanced by 1 compared to before the FIN

### Requirement: FIN Ordering Guarantee
The library SHALL prove that FIN is only sent after all preceding data from
SEND calls has been segmentized and placed on the network. RFC 793 §3.9 CLOSE
Call for ESTABLISHED: "Queue this until all preceding SENDs have been
segmentized, then form a FIN segment and send it." The TCP SHALL "reliably
deliver all buffers SENT before the connection was CLOSED" (RFC 793 §3.5).

#### Scenario: FIN after all data
- **WHEN** a user issues CLOSE with pending SEND data
- **THEN** all data is segmentized and sent before the FIN segment is emitted

### Requirement: TIME-WAIT Duration
The library SHALL prove that an endpoint in TIME-WAIT remains in TIME-WAIT
until the TIME-WAIT timeout fires. No user call or segment arrival (other than
a retransmitted FIN or a valid RST) causes an exit from TIME-WAIT before the
timeout.

Note: RST in TIME-WAIT causes immediate transition to CLOSED (RFC 793 §3.9
second check: CLOSING/LAST-ACK/TIME-WAIT + RST → CLOSED).

#### Scenario: TIME-WAIT persists
- **WHEN** an endpoint is in TIME-WAIT and no timeout or RST has arrived
- **THEN** the endpoint remains in TIME-WAIT

#### Scenario: RST in TIME-WAIT
- **WHEN** a valid RST arrives in TIME-WAIT
- **THEN** the endpoint transitions immediately to CLOSED

### Requirement: TIME-WAIT FIN Retransmission Handling
The library SHALL prove that if a retransmitted FIN arrives while in TIME-WAIT,
the endpoint ACKs it and restarts the 2×MSL timer (RFC 793 §3.9 eighth check,
TIME-WAIT state).

#### Scenario: Retransmitted FIN in TIME-WAIT
- **WHEN** a FIN arrives at an endpoint in TIME-WAIT
- **THEN** an ACK is sent and the TIME-WAIT timer is restarted
