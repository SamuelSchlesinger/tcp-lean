# TCP Formalization Fix Checklist

Work through every item in order. Do not stop until all items are checked off.
Run `lake build` after each phase to confirm zero `sorry` and no errors.

## Phase 1: Fix model bugs

- [x] 1.1 Fix duplicate ACK skipping window update
  - In `pipelineAck` (State.lean), ESTABLISHED branch: always call `ackUpdate`
    for non-future ACKs (ackAdvanceTcb is self-guarding). Remove the separate
    duplicate-ACK branch that returns `some ep` unchanged.
  - Apply the same fix to FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT, Closing branches.
  - Update `pipelineAck_preserves` proof in Invariants.lean.
  - `lake build` must pass.

- [x] 1.2 Fix SystemStep network model
  - In `SystemStep` (State.lean), replace `(seg : Segment) (rest : List Segment)
    (h_net : s.network = seg :: rest ∨ seg ∈ s.network)` with
    `(seg : Segment) (h_mem : seg ∈ s.network)` for deliverToA, deliverToB,
    and segmentLoss.
  - Post-delivery network becomes `s.network.erase seg ++ result.segments`.
  - Post-loss network becomes `s.network.erase seg`.
  - Remove `segmentDup`'s `rest` if it has one (it doesn't, just `h_mem`).
  - Update all `cases hStep` proofs in Invariants.lean.
  - `lake build` must pass.

- [x] 1.3 Fix data on SYN-ACK bypassing pipeline
  - In `processSegmentSynSent` (State.lean), when entering ESTABLISHED and the
    segment has data or FIN, route through `pipelinePostAck` (steps 6-8) instead
    of manually appending to recvBuffer.
  - Update `processSegmentSynSent_preserves` proof in Invariants.lean.
  - `lake build` must pass.

- [x] 1.4 Make segmentize respect the send window
  - In `segmentize` (State.lean), compute available bytes as
    `min(sendQueue.length, SND.WND - (SND.NXT - SND.UNA))` and only send that
    many. Leave the remainder in the queue.
  - Update `segmentize_preserves`, `processSend_preserves`, and
    `processClose_preserves` proofs.
  - `lake build` must pass.

## Phase 2: Close the invariant hole

- [x] 2.1 Prove send window bound invariant
  - Define `windowInvariant ep := SeqNum.le ep.tcb.sndNxt
    (ep.tcb.sndUna.add ep.tcb.sndWnd.toUInt32) = true`.
  - Prove it is preserved by every processing function.
  - `lake build` must pass.

- [x] 2.2 Remove blanket hypotheses from systemStep_preserves_invariant
  - Strengthen `endpointInvariant` to include both `SND.UNA <= SND.NXT` and the
    window bound.
  - Remove `h_userA` and `h_userB` parameters from
    `systemStep_preserves_invariant`. The proof should be fully unconditional.
  - `lake build` must pass.

- [x] 2.3 Prove SND.UNA monotonicity
  - Theorem: for any SystemStep, the new `SND.UNA` is `>=` the old `SND.UNA`
    (using SeqNum.le).
  - `lake build` must pass.

- [x] 2.4 Prove RCV.NXT monotonicity
  - Theorem: for any SystemStep, the new `RCV.NXT` is `>=` the old `RCV.NXT`
    (using SeqNum.le).
  - `lake build` must pass.

## Phase 3: Prove meaningful properties

- [x] 3.1 Prove ESTABLISHED requires handshake
  - Theorem: if endpoint A is ESTABLISHED in a system reachable from the initial
    state (both CLOSED, empty network), then a SYN and SYN-ACK were exchanged.
  - Define a handshake witness structure and show ESTABLISHED is only reachable
    through the appropriate processing functions.
  - `lake build` must pass.

- [x] 3.2 Document reassembly as a known limitation
  - Add a note in the whitepaper Known Deviations section explaining that the
    model assumes in-order segment delivery for data processing and does not
    implement reassembly.

- [x] 3.3 Update whitepaper
  - Reflect all Phase 1 bug fixes, Phase 2 invariants, and Phase 3 safety
    property in the whitepaper text. Ensure every theorem cited in the paper
    corresponds to a named Lean theorem.
  - Whitepaper must compile (`pdflatex`).

## Final validation

- [x] `lake build` succeeds with zero `sorry`
- [x] `git diff` reviewed for correctness
- [x] All changes committed
