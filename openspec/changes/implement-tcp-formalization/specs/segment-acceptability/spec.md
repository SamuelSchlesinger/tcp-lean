## ADDED Requirements

### Requirement: Segment Acceptability Predicate
The library SHALL define a `segmentAcceptable` predicate implementing the
four-case acceptability table from RFC 793 §3.3:

| SEG.LEN | RCV.WND | Test |
|---------|---------|------|
| 0       | 0       | `SEG.SEQ = RCV.NXT` |
| 0       | > 0     | `RCV.NXT ≤ SEG.SEQ < RCV.NXT + RCV.WND` |
| > 0     | 0       | not acceptable |
| > 0     | > 0     | `RCV.NXT ≤ SEG.SEQ < RCV.NXT + RCV.WND` OR `RCV.NXT ≤ SEG.SEQ + SEG.LEN - 1 < RCV.NXT + RCV.WND` |

All comparisons SHALL use `SeqNum.le` / `SeqNum.lt` (modular).

#### Scenario: Zero-length segment with zero window
- **WHEN** `SEG.LEN = 0` and `RCV.WND = 0` and `SEG.SEQ = RCV.NXT`
- **THEN** the segment is acceptable

#### Scenario: Zero-length segment with zero window, wrong seq
- **WHEN** `SEG.LEN = 0` and `RCV.WND = 0` and `SEG.SEQ ≠ RCV.NXT`
- **THEN** the segment is NOT acceptable

#### Scenario: Data segment with zero window
- **WHEN** `SEG.LEN > 0` and `RCV.WND = 0`
- **THEN** the segment is NOT acceptable regardless of `SEG.SEQ`

#### Scenario: Data segment start in window
- **WHEN** `SEG.LEN > 0` and `RCV.WND > 0` and `RCV.NXT ≤ SEG.SEQ < RCV.NXT + RCV.WND`
- **THEN** the segment is acceptable

#### Scenario: Data segment end in window
- **WHEN** `SEG.LEN > 0` and `RCV.WND > 0` and `SEG.SEQ` is before `RCV.NXT` but `SEG.SEQ + SEG.LEN - 1` falls within `[RCV.NXT, RCV.NXT + RCV.WND)`
- **THEN** the segment is acceptable (partial overlap)

### Requirement: ACK Acceptability Predicates
The library SHALL define two ACK acceptability predicates, reflecting the
different tests used in different states:

**ESTABLISHED and later states** (RFC 793 §3.9 fifth check, ESTABLISHED):
```
SND.UNA < SEG.ACK ≤ SND.NXT
```
(strict inequality on the left — `SEG.ACK = SND.UNA` is a duplicate ACK)

**SYN-RECEIVED state** (RFC 793 §3.9 fifth check, SYN-RECEIVED):
```
SND.UNA ≤ SEG.ACK ≤ SND.NXT
```
(non-strict on the left — the ACK may equal `SND.UNA` which is ISS)

Both SHALL use `SeqNum.lt` / `SeqNum.le` (modular).

#### Scenario: New ACK in ESTABLISHED
- **WHEN** `SEG.ACK` is strictly greater than `SND.UNA` and ≤ `SND.NXT`
- **THEN** the ACK is acceptable

#### Scenario: Duplicate ACK in ESTABLISHED
- **WHEN** `SEG.ACK ≤ SND.UNA`
- **THEN** the ACK is NOT acceptable (duplicate, can be ignored)

#### Scenario: Future ACK
- **WHEN** `SEG.ACK > SND.NXT`
- **THEN** the ACK is NOT acceptable (acks something not yet sent; send ACK and drop)

#### Scenario: ACK in SYN-RECEIVED allows equality
- **WHEN** `SEG.ACK = SND.UNA` in SYN-RECEIVED state
- **THEN** the ACK is acceptable (non-strict left bound)

### Requirement: Acceptability Lemmas
The library SHALL prove lemmas connecting acceptability predicates to TCB
invariants:
- If `ackAcceptable` holds and `SND.UNA` is advanced to `SEG.ACK`, then the
  new `SND.UNA ≤ SND.NXT` still holds
- A zero-length zero-window segment is acceptable if and only if
  `SEG.SEQ = RCV.NXT`
- A data-bearing segment is never acceptable when `RCV.WND = 0`

#### Scenario: ACK advance preserves invariant
- **WHEN** an acceptable ACK is processed and `SND.UNA` updated to `SEG.ACK`
- **THEN** the updated TCB satisfies `SND.UNA ≤ SND.NXT`
