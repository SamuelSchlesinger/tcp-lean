import Tcp.SeqNum
import Tcp.Types
import Tcp.Acceptability

/-!
# TCP Connection State Machine

TCP endpoint structure, two-endpoint system model, and the full event-processing
step function implementing RFC 793 §3.9.

This module defines:
- `TcpEndpoint`: a single TCP endpoint's complete state
- `System`: two communicating endpoints with an explicit network
- Event processing functions for all user calls, segment arrival (CLOSED,
  LISTEN, SYN-SENT, and the 8-check pipeline for remaining states), and
  timeouts
- `SystemStep`: the inductive type relating system states via atomic transitions
-/

namespace Tcp

open SeqNum

-- ============================================================================
-- TCP Endpoint — RFC 793 §3.2
-- ============================================================================

/-- Default receive window size (for simplicity, a fixed constant). -/
def defaultRcvWnd : UInt16 := 65535

/-- A TCP endpoint's complete state. Bundles the connection state, TCB,
    origin mode, buffers, and queues.

    RFC 793 §3.2: "Among the variables stored in the TCB are the local and
    remote socket numbers... pointers to the user's send and receive buffers,
    pointers to the retransmit queue and to the current segment." -/
structure TcpEndpoint where
  /-- Current connection state. RFC 793 §3.2 -/
  state : TcpState := .Closed
  /-- Transmission control block variables. -/
  tcb : Tcb := {
    sndUna := ⟨0⟩, sndNxt := ⟨0⟩, sndWnd := 0, sndUp := ⟨0⟩,
    sndWl1 := ⟨0⟩, sndWl2 := ⟨0⟩, iss := ⟨0⟩,
    rcvNxt := ⟨0⟩, rcvWnd := 0, rcvUp := ⟨0⟩, irs := ⟨0⟩
  }
  /-- Whether this connection originated from active or passive OPEN.
      Needed for RST handling in SYN-RECEIVED (RFC 793 §3.9 second check). -/
  openMode : Option OpenMode := none
  /-- Data queued by SEND calls, not yet transmitted. -/
  sendQueue : List UInt8 := []
  /-- In-order received data awaiting user RECEIVE. -/
  recvBuffer : List UInt8 := []
  /-- Out-of-order segments held for reassembly.
      RFC 793 §3.9: "Segments with higher beginning sequence numbers may
      be held for later processing." -/
  reassemblyBuf : List Segment := []
  /-- Unacknowledged segments for retransmission. -/
  retxQueue : List Segment := []
  /-- Whether a FIN has been sent. Used for FIN acknowledgment detection. -/
  finSent : Bool := false
  /-- The sequence number of the FIN we sent, if any. -/
  finSeqNum : Option SeqNum := none
deriving Repr

/-- A closed (empty) endpoint, equivalent to having no TCB. -/
def closedEndpoint : TcpEndpoint :=
  { state := .Closed
    tcb := { sndUna := ⟨0⟩, sndNxt := ⟨0⟩, sndWnd := 0, sndUp := ⟨0⟩,
             sndWl1 := ⟨0⟩, sndWl2 := ⟨0⟩, iss := ⟨0⟩,
             rcvNxt := ⟨0⟩, rcvWnd := 0, rcvUp := ⟨0⟩, irs := ⟨0⟩ }
    openMode := none
    sendQueue := []
    recvBuffer := []
    reassemblyBuf := []
    retxQueue := []
    finSent := false
    finSeqNum := none }

-- ============================================================================
-- Two-Endpoint System Model — design decision D3
-- ============================================================================

/-- A system of two communicating TCP endpoints with an explicit network.
    The network is a list of in-flight segments treated as an unordered
    multiset: any element may be delivered next.

    This is the standard approach in protocol verification (cf. TLA+ TCP spec).
    Segment loss, duplication, and reordering are modeled via `SystemStep`. -/
structure System where
  endpointA : TcpEndpoint := {}
  endpointB : TcpEndpoint := {}
  network : List Segment := []
deriving Repr

-- ============================================================================
-- Helper: create a segment
-- ============================================================================

/-- Create a minimal segment with given fields. -/
def mkSegment (seq ackNum : SeqNum) (ctl : ControlBits) (window : UInt16)
    (data : List UInt8 := []) : Segment :=
  { srcPort := 0, dstPort := 0, seq, ackNum, ctl, window, data }

-- ============================================================================
-- Event Processing — RFC 793 §3.9
-- ============================================================================

/-- Result of processing an event on an endpoint: the updated endpoint
    and any segments to emit onto the network. -/
structure ProcessResult where
  endpoint : TcpEndpoint
  segments : List Segment := []
  response : Option UserResponse := none
deriving Repr

/-- A fresh TCB initialized for a new connection. -/
def freshTcb (iss : SeqNum) : Tcb :=
  { sndUna := iss, sndNxt := iss, sndWnd := 0, sndUp := ⟨0⟩,
    sndWl1 := ⟨0⟩, sndWl2 := ⟨0⟩, iss,
    rcvNxt := ⟨0⟩, rcvWnd := defaultRcvWnd, rcvUp := ⟨0⟩, irs := ⟨0⟩ }

-- ============================================================================
-- OPEN Call — RFC 793 §3.9 OPEN Call
-- ============================================================================

/-- Process an OPEN call.
    RFC 793 §3.9 OPEN Call:
    - CLOSED + passive → create TCB, enter LISTEN
    - CLOSED + active → create TCB, select ISS, send SYN, enter SYN-SENT
    - LISTEN + active → select ISS, send SYN, enter SYN-SENT
    - All other states → error (connection already exists) -/
def processOpen (ep : TcpEndpoint) (mode : OpenMode) (iss : SeqNum)
    : ProcessResult :=
  match ep.state with
  | .Closed =>
    match mode with
    | .Passive =>
      { endpoint := { ep with
          state := .Listen
          tcb := freshTcb iss
          openMode := some .Passive }
        response := some .Ok }
    | .Active =>
      let tcb := { freshTcb iss with sndNxt := iss.add 1 }
      let syn := mkSegment iss ⟨0⟩ { syn := true } defaultRcvWnd
      { endpoint := { ep with
          state := .SynSent
          tcb := tcb
          openMode := some .Active }
        segments := [syn]
        response := some .Ok }
  | .Listen =>
    match mode with
    | .Active =>
      let tcb := { ep.tcb with sndNxt := iss.add 1, iss := iss, sndUna := iss }
      let syn := mkSegment iss ⟨0⟩ { syn := true } defaultRcvWnd
      { endpoint := { ep with
          state := .SynSent
          tcb := tcb
          openMode := some .Active }
        segments := [syn]
        response := some .Ok }
    | .Passive =>
      { endpoint := ep
        response := some (.Error "connection already exists") }
  | _ =>
    { endpoint := ep
      response := some (.Error "connection already exists") }

-- ============================================================================
-- SEND Call — RFC 793 §3.9 SEND Call
-- ============================================================================

/-- Segmentize data from the send queue into segments, respecting the send
    window. Returns updated endpoint and list of segments to emit. -/
def segmentize (ep : TcpEndpoint) : TcpEndpoint × List Segment :=
  if ep.sendQueue.isEmpty then (ep, [])
  else
    let seg := mkSegment ep.tcb.sndNxt ep.tcb.rcvNxt
      { ack := true } ep.tcb.rcvWnd ep.sendQueue
    let newNxt := ep.tcb.sndNxt.add ep.sendQueue.length.toUInt32
    let ep' := { ep with
      tcb := { ep.tcb with sndNxt := newNxt }
      sendQueue := []
      retxQueue := ep.retxQueue ++ [seg] }
    (ep', [seg])

/-- Process a SEND call.
    RFC 793 §3.9 SEND Call:
    - CLOSED → error
    - LISTEN → switch to active, send SYN, queue data for after ESTABLISHED
    - SYN-SENT, SYN-RECEIVED → queue data
    - ESTABLISHED, CLOSE-WAIT → segmentize and send
    - FIN-WAIT-*, CLOSING, LAST-ACK, TIME-WAIT → error (connection closing) -/
def processSend (ep : TcpEndpoint) (data : List UInt8) : ProcessResult :=
  match ep.state with
  | .Closed =>
    { endpoint := ep, response := some (.Error "connection does not exist") }
  | .Listen =>
    { endpoint := { ep with sendQueue := ep.sendQueue ++ data }
      response := some (.Error "SEND in LISTEN: queue data, switch to active on SYN") }
  | .SynSent | .SynReceived =>
    { endpoint := { ep with sendQueue := ep.sendQueue ++ data }
      response := some .Ok }
  | .Established | .CloseWait =>
    let ep' := { ep with sendQueue := ep.sendQueue ++ data }
    let (ep'', segs) := segmentize ep'
    { endpoint := ep'', segments := segs, response := some .Ok }
  | .FinWait1 | .FinWait2 | .Closing | .LastAck | .TimeWait =>
    { endpoint := ep, response := some (.Error "connection closing") }

-- ============================================================================
-- RECEIVE Call — RFC 793 §3.9 RECEIVE Call
-- ============================================================================

/-- Process a RECEIVE call.
    RFC 793 §3.9 RECEIVE Call:
    - CLOSED → error
    - LISTEN, SYN-SENT, SYN-RECEIVED → queue request for after ESTABLISHED
    - ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2 → deliver buffered data
    - CLOSE-WAIT → deliver remaining data or error if none
    - CLOSING, LAST-ACK, TIME-WAIT → error -/
def processReceive (ep : TcpEndpoint) : ProcessResult :=
  match ep.state with
  | .Closed =>
    { endpoint := ep, response := some (.Error "connection does not exist") }
  | .Listen | .SynSent | .SynReceived =>
    { endpoint := ep, response := some (.Error "insufficient data, request queued") }
  | .Established | .FinWait1 | .FinWait2 =>
    if ep.recvBuffer.isEmpty then
      { endpoint := ep, response := some (.Error "no data available") }
    else
      { endpoint := { ep with recvBuffer := [] }
        response := some (.Data ep.recvBuffer) }
  | .CloseWait =>
    if ep.recvBuffer.isEmpty then
      { endpoint := ep, response := some (.Error "connection closing, no data") }
    else
      { endpoint := { ep with recvBuffer := [] }
        response := some (.Data ep.recvBuffer) }
  | .Closing | .LastAck | .TimeWait =>
    { endpoint := ep, response := some (.Error "connection closing") }

-- ============================================================================
-- CLOSE Call — RFC 793 §3.9 CLOSE Call
-- ============================================================================

/-- Process a CLOSE call.
    RFC 793 §3.9 CLOSE Call:
    - CLOSED → error
    - LISTEN → delete TCB, enter CLOSED
    - SYN-SENT → delete TCB, enter CLOSED
    - SYN-RECEIVED → if no pending data, send FIN, enter FIN-WAIT-1;
                      else queue for after ESTABLISHED
    - ESTABLISHED → send FIN (after pending SENDs), enter FIN-WAIT-1
    - FIN-WAIT-1, FIN-WAIT-2 → error (already closing)
    - CLOSE-WAIT → send FIN (after pending SENDs), enter LAST-ACK
      (RFC 793 Figure 6; the §3.9 text says "CLOSING" but Figure 6 is
      authoritative: CLOSE-WAIT → LAST-ACK)
    - CLOSING, LAST-ACK, TIME-WAIT → error -/
def processClose (ep : TcpEndpoint) : ProcessResult :=
  match ep.state with
  | .Closed =>
    { endpoint := ep, response := some (.Error "connection does not exist") }
  | .Listen | .SynSent =>
    { endpoint := closedEndpoint
      response := some .Ok }
  | .SynReceived =>
    if ep.sendQueue.isEmpty then
      let finSeq := ep.tcb.sndNxt
      let fin := mkSegment finSeq ep.tcb.rcvNxt { ack := true, fin := true } ep.tcb.rcvWnd
      { endpoint := { ep with
          state := .FinWait1
          tcb := { ep.tcb with sndNxt := finSeq.add 1 }
          finSent := true
          finSeqNum := some finSeq }
        segments := [fin]
        response := some .Ok }
    else
      -- Queue the CLOSE for after data is sent
      { endpoint := ep, response := some .Ok }
  | .Established =>
    -- First segmentize any pending data, then send FIN
    let (ep', dataSegs) := segmentize ep
    let finSeq := ep'.tcb.sndNxt
    let fin := mkSegment finSeq ep'.tcb.rcvNxt { ack := true, fin := true } ep'.tcb.rcvWnd
    { endpoint := { ep' with
        state := .FinWait1
        tcb := { ep'.tcb with sndNxt := finSeq.add 1 }
        finSent := true
        finSeqNum := some finSeq }
      segments := dataSegs ++ [fin]
      response := some .Ok }
  | .FinWait1 | .FinWait2 =>
    { endpoint := ep, response := some (.Error "connection closing") }
  | .CloseWait =>
    let (ep', dataSegs) := segmentize ep
    let finSeq := ep'.tcb.sndNxt
    let fin := mkSegment finSeq ep'.tcb.rcvNxt { ack := true, fin := true } ep'.tcb.rcvWnd
    { endpoint := { ep' with
        state := .LastAck
        tcb := { ep'.tcb with sndNxt := finSeq.add 1 }
        finSent := true
        finSeqNum := some finSeq }
      segments := dataSegs ++ [fin]
      response := some .Ok }
  | .Closing | .LastAck | .TimeWait =>
    { endpoint := ep, response := some (.Error "connection closing") }

-- ============================================================================
-- ABORT Call — RFC 793 §3.9 ABORT Call
-- ============================================================================

/-- Process an ABORT call.
    RFC 793 §3.9 ABORT Call:
    - CLOSED → error
    - LISTEN, SYN-SENT → delete TCB, enter CLOSED
    - SYN-RECEIVED, ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT →
      send RST (SEQ=SND.NXT), flush queues, enter CLOSED
    - CLOSING, LAST-ACK, TIME-WAIT → delete TCB, enter CLOSED -/
def processAbort (ep : TcpEndpoint) : ProcessResult :=
  match ep.state with
  | .Closed =>
    { endpoint := ep, response := some (.Error "connection does not exist") }
  | .Listen | .SynSent =>
    { endpoint := closedEndpoint
      response := some .Ok }
  | .SynReceived | .Established | .FinWait1 | .FinWait2 | .CloseWait =>
    let rst := mkSegment ep.tcb.sndNxt ⟨0⟩ { rst := true } 0
    { endpoint := closedEndpoint
      segments := [rst]
      response := some .Ok }
  | .Closing | .LastAck | .TimeWait =>
    { endpoint := closedEndpoint
      response := some .Ok }

-- ============================================================================
-- SEGMENT ARRIVES — CLOSED State — RFC 793 §3.9
-- ============================================================================

/-- Process segment arrival in CLOSED state.
    RFC 793 §3.9 SEGMENT ARRIVES, CLOSED:
    - RST → discard
    - ACK set → respond with RST: <SEQ=SEG.ACK><CTL=RST>
    - No ACK → respond with RST: <SEQ=0><ACK=SEG.SEQ+SEG.LEN><CTL=RST,ACK> -/
def processSegmentClosed (ep : TcpEndpoint) (seg : Segment) : ProcessResult :=
  if seg.ctl.rst then
    { endpoint := ep }
  else if seg.ctl.ack then
    let rst := mkSegment seg.ackNum ⟨0⟩ { rst := true } 0
    { endpoint := ep, segments := [rst] }
  else
    let ackVal := seg.seq.add seg.len
    let rst := mkSegment ⟨0⟩ ackVal { rst := true, ack := true } 0
    { endpoint := ep, segments := [rst] }

-- ============================================================================
-- SEGMENT ARRIVES — LISTEN State — RFC 793 §3.9
-- ============================================================================

/-- Process segment arrival in LISTEN state.
    RFC 793 §3.9 SEGMENT ARRIVES, LISTEN:
    1. RST → ignore
    2. ACK → send RST (bad: no connection to ACK)
    3. SYN → set RCV.NXT=SEG.SEQ+1, IRS=SEG.SEQ, select ISS, send SYN-ACK,
       set SND.NXT=ISS+1, SND.UNA=ISS, enter SYN-RECEIVED.
       Any data on the SYN is queued for processing after ESTABLISHED.
    4. Other → drop -/
def processSegmentListen (ep : TcpEndpoint) (seg : Segment) (iss : SeqNum)
    : ProcessResult :=
  if seg.ctl.rst then
    { endpoint := ep }
  else if seg.ctl.ack then
    let rst := mkSegment seg.ackNum ⟨0⟩ { rst := true } 0
    { endpoint := ep, segments := [rst] }
  else if seg.ctl.syn then
    let rcvNxt := seg.seq.add 1
    let tcb : Tcb := {
      sndUna := iss, sndNxt := iss.add 1, sndWnd := seg.window,
      sndUp := ⟨0⟩, sndWl1 := seg.seq, sndWl2 := seg.ackNum, iss,
      rcvNxt, rcvWnd := defaultRcvWnd, rcvUp := ⟨0⟩, irs := seg.seq
    }
    let synAck := mkSegment iss rcvNxt { syn := true, ack := true } defaultRcvWnd
    -- Data piggybacked on SYN is buffered in reassembly, not delivered yet
    -- RFC 793 §3.4: data on SYN queued until ESTABLISHED
    let reassembly := if seg.data.isEmpty then ep.reassemblyBuf
                      else ep.reassemblyBuf ++ [seg]
    { endpoint := { ep with
        state := .SynReceived
        tcb := tcb
        openMode := some .Passive
        reassemblyBuf := reassembly }
      segments := [synAck] }
  else
    { endpoint := ep }

-- ============================================================================
-- SEGMENT ARRIVES — SYN-SENT State — RFC 793 §3.9
-- ============================================================================

/-- Process segment arrival in SYN-SENT state.
    RFC 793 §3.9 SEGMENT ARRIVES, SYN-SENT (5-step pipeline):
    1. ACK check: if ACK, reject if SEG.ACK ≤ ISS or SEG.ACK > SND.NXT
    2. RST check: if ACK acceptable, abort; else drop
    3. Security check: skipped (D9)
    4. SYN check: if SYN, set RCV.NXT, IRS, advance SND.UNA;
       - if SND.UNA > ISS (our SYN ACKed) → ESTABLISHED, send ACK
         If segment has data/controls, continue at step 6 (URG/text/FIN)
       - else → SYN-RECEIVED, send SYN-ACK
    5. No SYN → drop -/
def processSegmentSynSent (ep : TcpEndpoint) (seg : Segment) : ProcessResult :=
  -- Step 1: ACK check
  let ackOk := if seg.ctl.ack then
    -- RFC 793 §3.9: "If SEG.ACK =< ISS, or SEG.ACK > SND.NXT"
    SeqNum.lt ep.tcb.iss seg.ackNum && SeqNum.le seg.ackNum ep.tcb.sndNxt
  else true  -- no ACK is fine (simultaneous open)

  if !ackOk then
    -- Bad ACK
    if seg.ctl.rst then
      { endpoint := ep }  -- drop
    else
      let rst := mkSegment seg.ackNum ⟨0⟩ { rst := true } 0
      { endpoint := ep, segments := [rst] }
  else
    -- Step 2: RST check
    if seg.ctl.rst then
      if seg.ctl.ack then
        -- Acceptable ACK + RST → abort
        { endpoint := closedEndpoint
          response := some (.Error "connection refused") }
      else
        { endpoint := ep }  -- RST without ACK, drop
    -- Step 3: security check skipped (D9)
    -- Step 4: SYN check
    else if seg.ctl.syn then
      let rcvNxt := seg.seq.add 1
      let newTcb := { ep.tcb with
        rcvNxt := rcvNxt, irs := seg.seq,
        rcvUp := ⟨0⟩ }
      -- Advance SND.UNA if ACK present
      let tcb2 : Tcb := if seg.ctl.ack then
        { newTcb with sndUna := seg.ackNum
                      sndWnd := seg.window
                      sndWl1 := seg.seq
                      sndWl2 := seg.ackNum }
      else newTcb
      if SeqNum.lt tcb2.iss tcb2.sndUna then
        -- Our SYN has been ACKed → ESTABLISHED
        let ackSeg := mkSegment tcb2.sndNxt rcvNxt { ack := true } defaultRcvWnd
        -- RFC 793 §3.9 SYN-SENT fourth check: "if the segment contains
        -- additional data or controls, continue processing at the sixth
        -- step below where the URG bit is checked"
        -- Process data on the SYN-ACK (step 7: segment text)
        let recvBuf := if seg.data.isEmpty then ep.recvBuffer
                       else ep.recvBuffer ++ seg.data
        let tcb3 : Tcb := if !seg.data.isEmpty then
          { tcb2 with rcvNxt := rcvNxt.add seg.data.length.toUInt32 }
        else tcb2
        { endpoint := { ep with
            state := .Established
            tcb := tcb3
            openMode := ep.openMode
            recvBuffer := recvBuf }
          segments := [ackSeg] }
      else
        -- Simultaneous open → SYN-RECEIVED
        let synAck := mkSegment ep.tcb.iss rcvNxt { syn := true, ack := true } defaultRcvWnd
        { endpoint := { ep with
            state := .SynReceived
            tcb := newTcb
            openMode := some .Active }
          segments := [synAck] }
    else
      -- Step 5: no SYN → drop
      { endpoint := ep }

-- ============================================================================
-- SEGMENT ARRIVES — Otherwise (Decomposed 8-check pipeline) — RFC 793 §3.9
-- ============================================================================

/-- Remove fully acknowledged segments from the retransmission queue.
    A segment is fully acknowledged when `ack ≥ seg.seq + seg.len` (modular). -/
def removeAcked (retxQueue : List Segment) (ack : SeqNum) : List Segment :=
  retxQueue.filter fun seg =>
    -- Keep if NOT fully acknowledged
    !SeqNum.le (seg.seq.add seg.len) ack

@[simp]
theorem removeAcked_nil (ack : SeqNum) : removeAcked [] ack = [] := rfl

-- ============================================================================
-- Common ACK Update Logic
-- ============================================================================

/-- Conditionally advance SND.UNA to SEG.ACK if the ACK is in range.
    RFC 793 §3.9 fifth check: "set SND.UNA <- SEG.ACK". -/
def ackAdvanceTcb (tcb : Tcb) (seg : Segment) : Tcb :=
  if SeqNum.lt tcb.sndUna seg.ackNum && SeqNum.le seg.ackNum tcb.sndNxt then
    { tcb with sndUna := seg.ackNum }
  else tcb

/-- Conditionally update the send window variables.
    RFC 793 §3.9 fifth check, window update rule. -/
def windowUpdateTcb (tcb : Tcb) (seg : Segment) : Tcb :=
  if SeqNum.lt tcb.sndWl1 seg.seq ||
     (tcb.sndWl1 == seg.seq && SeqNum.le tcb.sndWl2 seg.ackNum) then
    { tcb with sndWnd := seg.window, sndWl1 := seg.seq, sndWl2 := seg.ackNum }
  else tcb

@[simp] theorem ackAdvanceTcb_sndNxt (tcb : Tcb) (seg : Segment) :
    (ackAdvanceTcb tcb seg).sndNxt = tcb.sndNxt := by
  simp only [ackAdvanceTcb]; split <;> simp_all

@[simp] theorem windowUpdateTcb_sndNxt (tcb : Tcb) (seg : Segment) :
    (windowUpdateTcb tcb seg).sndNxt = tcb.sndNxt := by
  simp only [windowUpdateTcb]; split <;> simp_all

@[simp] theorem windowUpdateTcb_sndUna (tcb : Tcb) (seg : Segment) :
    (windowUpdateTcb tcb seg).sndUna = tcb.sndUna := by
  simp only [windowUpdateTcb]; split <;> simp_all

/-- Common ACK update logic for ESTABLISHED-like states: conditionally advance
    SND.UNA, remove acknowledged segments, apply window update.
    RFC 793 §3.9 fifth check. -/
def ackUpdate (ep : TcpEndpoint) (seg : Segment) : TcpEndpoint :=
  let tcb1 := ackAdvanceTcb ep.tcb seg
  let tcb2 := windowUpdateTcb tcb1 seg
  { ep with tcb := tcb2, retxQueue := removeAcked ep.retxQueue seg.ackNum }

-- ============================================================================
-- Pipeline Step 1-4: Pre-ACK Checks
-- ============================================================================

/-- Steps 1-4 of the 8-check pipeline: sequence check, RST, SYN, ACK-bit check.
    Returns `some result` to terminate the pipeline, `none` to continue to
    ACK processing.

    RFC 793 §3.9 SEGMENT ARRIVES, "Otherwise":
    1. Sequence check (acceptability)
    2. RST check (state-dependent)
    3. Security check (skipped per D9)
    4. SYN check -/
def pipelinePreAck (ep : TcpEndpoint) (seg : Segment) : Option ProcessResult :=
  -- Step 1: Sequence check
  if !segmentAcceptable ep.tcb seg then
    if seg.ctl.rst then some { endpoint := ep }
    else
      let ackSeg := mkSegment ep.tcb.sndNxt ep.tcb.rcvNxt { ack := true } ep.tcb.rcvWnd
      some { endpoint := ep, segments := [ackSeg] }
  -- Step 2: RST check
  else if seg.ctl.rst then
    match ep.state with
    | .SynReceived =>
      match ep.openMode with
      | some .Passive =>
        some { endpoint := { ep with state := .Listen, openMode := some .Passive }
               response := none }
      | _ =>
        some { endpoint := closedEndpoint
               response := some (.Error "connection refused") }
    | .Established | .FinWait1 | .FinWait2 | .CloseWait =>
      some { endpoint := closedEndpoint
             response := some (.Error "connection reset") }
    | .Closing | .LastAck | .TimeWait =>
      some { endpoint := closedEndpoint }
    | _ => some { endpoint := ep }
  -- Step 3: Security check (skipped per D9)
  -- Step 4: SYN check
  else if seg.ctl.syn then
    let rst := mkSegment ep.tcb.sndNxt ⟨0⟩ { rst := true } 0
    some { endpoint := closedEndpoint
           segments := [rst]
           response := some (.Error "connection reset by SYN in window") }
  -- ACK bit must be set to continue
  else if !seg.ctl.ack then
    some { endpoint := ep }
  else
    none

-- ============================================================================
-- Pipeline Step 5: ACK Processing
-- ============================================================================

/-- Step 5: ACK processing (state-dependent).
    Returns `some ep'` on acceptance (with updated TCB), `none` on rejection.
    RFC 793 §3.9 fifth check. -/
def pipelineAck (ep : TcpEndpoint) (seg : Segment) : Option TcpEndpoint :=
  match ep.state with
  | .SynReceived =>
    -- RFC 793 §3.9: "If SND.UNA =< SEG.ACK =< SND.NXT then enter ESTABLISHED"
    if SeqNum.le ep.tcb.sndUna seg.ackNum && SeqNum.le seg.ackNum ep.tcb.sndNxt then
      let newTcb := { ep.tcb with
        sndUna := seg.ackNum
        sndWnd := seg.window
        sndWl1 := seg.seq
        sndWl2 := seg.ackNum }
      some { ep with state := .Established, tcb := newTcb }
    else
      none
  | .Established =>
    -- RFC 793 §3.9: "If SND.UNA < SEG.ACK =< SND.NXT then, set SND.UNA <- SEG.ACK"
    if SeqNum.lt ep.tcb.sndUna seg.ackNum && SeqNum.le seg.ackNum ep.tcb.sndNxt then
      some (ackUpdate ep seg)
    else if SeqNum.lt ep.tcb.sndNxt seg.ackNum then
      none  -- future ACK
    else
      some ep  -- duplicate ACK
  | .FinWait1 =>
    let ep' := ackUpdate ep seg
    let finAcked := match ep.finSeqNum with
      | some fseq => SeqNum.lt fseq seg.ackNum
      | none => false
    let newState := if finAcked then TcpState.FinWait2 else TcpState.FinWait1
    some { ep' with state := newState }
  | .FinWait2 =>
    some (ackUpdate ep seg)
  | .CloseWait =>
    some (ackUpdate ep seg)
  | .Closing =>
    -- RFC 793 §3.9: "if the ACK acknowledges our FIN then enter TIME-WAIT"
    let finAcked := match ep.finSeqNum with
      | some fseq => SeqNum.lt fseq seg.ackNum
      | none => false
    if finAcked then
      some { ep with state := .TimeWait }
    else
      some ep
  | .LastAck =>
    -- RFC 793 §3.9: "if our FIN is now acknowledged, delete TCB, enter CLOSED"
    let finAcked := match ep.finSeqNum with
      | some fseq => SeqNum.lt fseq seg.ackNum
      | none => false
    if finAcked then
      some closedEndpoint
    else
      some ep
  | .TimeWait =>
    some ep
  | _ => some ep

/-- Handle ACK rejection from step 5.
    SYN-RECEIVED → send RST; other states → send ACK.
    RFC 793 §3.9 fifth check. -/
def pipelineAckReject (ep : TcpEndpoint) (seg : Segment) : ProcessResult :=
  match ep.state with
  | .SynReceived =>
    let rst := mkSegment seg.ackNum ⟨0⟩ { rst := true } 0
    { endpoint := ep, segments := [rst] }
  | _ =>
    let ackSeg := mkSegment ep.tcb.sndNxt ep.tcb.rcvNxt { ack := true } ep.tcb.rcvWnd
    { endpoint := ep, segments := [ackSeg] }

-- ============================================================================
-- Pipeline Step 6: URG Check
-- ============================================================================

/-- Step 6: URG check. Updates RCV.UP if URG bit set.
    RFC 793 §3.9 sixth check. Only processed in ESTABLISHED, FIN-WAIT-1/2. -/
def pipelineUrg (ep : TcpEndpoint) (seg : Segment) : TcpEndpoint :=
  match ep.state with
  | .Established | .FinWait1 | .FinWait2 =>
    if seg.ctl.urg then
      let newUp := if SeqNum.lt ep.tcb.rcvUp (ep.tcb.rcvNxt.add seg.urgPtr.toUInt32) then
        ep.tcb.rcvNxt.add seg.urgPtr.toUInt32
      else ep.tcb.rcvUp
      { ep with tcb := { ep.tcb with rcvUp := newUp } }
    else ep
  | _ => ep

@[simp]
theorem pipelineUrg_state (ep : TcpEndpoint) (seg : Segment) :
    (pipelineUrg ep seg).state = ep.state := by
  simp only [pipelineUrg]; split <;> (try split) <;> simp_all

-- ============================================================================
-- Pipeline Step 7: Segment Text
-- ============================================================================

/-- Step 7: Segment text processing. Buffers data and advances RCV.NXT.
    RFC 793 §3.9 seventh check. Only in ESTABLISHED, FIN-WAIT-1/2. -/
def pipelineText (ep : TcpEndpoint) (seg : Segment) : TcpEndpoint × Bool :=
  match ep.state with
  | .Established | .FinWait1 | .FinWait2 =>
    if !seg.data.isEmpty then
      let newRcvNxt := ep.tcb.rcvNxt.add seg.data.length.toUInt32
      ({ ep with
        tcb := { ep.tcb with rcvNxt := newRcvNxt }
        recvBuffer := ep.recvBuffer ++ seg.data }, true)
    else (ep, false)
  | _ => (ep, false)

@[simp]
theorem pipelineText_state (ep : TcpEndpoint) (seg : Segment) :
    (pipelineText ep seg).1.state = ep.state := by
  simp only [pipelineText]; split <;> (try split) <;> simp_all

-- ============================================================================
-- Pipeline Step 8: FIN Check
-- ============================================================================

/-- Step 8: FIN check. Advances RCV.NXT over the FIN and transitions state.
    RFC 793 §3.9 eighth check: "If the FIN bit is set..." -/
def pipelineFin (ep : TcpEndpoint) (seg : Segment) (needAck : Bool) : ProcessResult :=
  if seg.ctl.fin then
    let newRcvNxt := ep.tcb.rcvNxt.add 1
    let ep' := { ep with tcb := { ep.tcb with rcvNxt := newRcvNxt } }
    let ackSeg := mkSegment ep'.tcb.sndNxt newRcvNxt { ack := true } ep'.tcb.rcvWnd
    match ep'.state with
    | .SynReceived | .Established =>
      { endpoint := { ep' with state := .CloseWait }
        segments := [ackSeg] }
    | .FinWait1 =>
      let finAcked := match ep'.finSeqNum with
        | some fseq => SeqNum.lt fseq seg.ackNum
        | none => false
      if finAcked then
        { endpoint := { ep' with state := .TimeWait }
          segments := [ackSeg] }
      else
        { endpoint := { ep' with state := .Closing }
          segments := [ackSeg] }
    | .FinWait2 =>
      { endpoint := { ep' with state := .TimeWait }
        segments := [ackSeg] }
    | _ =>
      -- CLOSE-WAIT, CLOSING, LAST-ACK, TIME-WAIT: remain in state
      { endpoint := ep', segments := [ackSeg] }
  else
    if needAck then
      let ackSeg := mkSegment ep.tcb.sndNxt ep.tcb.rcvNxt { ack := true } ep.tcb.rcvWnd
      { endpoint := ep, segments := [ackSeg] }
    else
      { endpoint := ep }

-- ============================================================================
-- Pipeline Steps 6-8: Post-ACK Processing (Composed)
-- ============================================================================

/-- Steps 6-8 composed: URG check, segment text, FIN check.
    RFC 793 §3.9 sixth, seventh, eighth checks. -/
def pipelinePostAck (ep : TcpEndpoint) (seg : Segment) : ProcessResult :=
  let ep' := pipelineUrg ep seg
  let (ep', needAck) := pipelineText ep' seg
  pipelineFin ep' seg needAck

-- ============================================================================
-- Composed Pipeline
-- ============================================================================

/-- Process segment arrival in states SYN-RECEIVED through TIME-WAIT.
    RFC 793 §3.9 SEGMENT ARRIVES, "Otherwise" — the 8-check pipeline,
    decomposed into `pipelinePreAck`, `pipelineAck`, `pipelineAckReject`,
    and `pipelinePostAck` for composable invariant reasoning. -/
def processSegmentOtherwise (ep : TcpEndpoint) (seg : Segment) : ProcessResult :=
  match pipelinePreAck ep seg with
  | some result => result
  | none =>
    match pipelineAck ep seg with
    | none => pipelineAckReject ep seg
    | some ep' => pipelinePostAck ep' seg

-- ============================================================================
-- Unified segment processing dispatcher
-- ============================================================================

/-- Process an incoming segment on an endpoint. Dispatches to the appropriate
    handler based on the endpoint's current state.

    RFC 793 §3.9 SEGMENT ARRIVES. The `iss` parameter is only used when in
    LISTEN state (to provide an ISS for the SYN-ACK). -/
def processSegment (ep : TcpEndpoint) (seg : Segment) (iss : SeqNum := ⟨0⟩)
    : ProcessResult :=
  match ep.state with
  | .Closed => processSegmentClosed ep seg
  | .Listen => processSegmentListen ep seg iss
  | .SynSent => processSegmentSynSent ep seg
  | _ => processSegmentOtherwise ep seg

-- ============================================================================
-- User call dispatcher
-- ============================================================================

/-- Process a user call on an endpoint.
    RFC 793 §3.9: OPEN, SEND, RECEIVE, CLOSE, ABORT, STATUS calls. -/
def processUserCall (ep : TcpEndpoint) (call : UserCall) : ProcessResult :=
  match call with
  | .Open mode iss => processOpen ep mode iss
  | .Send data => processSend ep data
  | .Receive => processReceive ep
  | .Close => processClose ep
  | .Abort => processAbort ep
  | .Status => { endpoint := ep, response := some (.StateInfo ep.state) }

-- ============================================================================
-- Timeout Processing — RFC 793 §3.9
-- ============================================================================

/-- Process a timeout event.
    RFC 793 §3.9 Timeouts:
    - USER TIMEOUT: flush queues, signal error, enter CLOSED
    - RETRANSMISSION TIMEOUT: resend head of retransmission queue
    - TIME-WAIT TIMEOUT: delete TCB, enter CLOSED -/
def processTimeout (ep : TcpEndpoint) (kind : TimeoutKind) : ProcessResult :=
  match kind with
  | .UserTimeout =>
    { endpoint := closedEndpoint
      response := some (.Error "connection timed out") }
  | .Retransmission =>
    match ep.retxQueue with
    | [] => { endpoint := ep }
    | seg :: _ => { endpoint := ep, segments := [seg] }
  | .TimeWait =>
    match ep.state with
    | .TimeWait =>
      { endpoint := closedEndpoint }
    | _ => { endpoint := ep }

-- ============================================================================
-- SystemStep — Relating System states
-- ============================================================================

/-- One atomic transition of the two-endpoint system.
    Each step advances the system by exactly one action. -/
inductive SystemStep : System → System → Prop where
  /-- Deliver a segment from the network to endpoint A. -/
  | deliverToA (s : System) (seg : Segment) (rest : List Segment)
    (h_net : s.network = seg :: rest ∨ seg ∈ s.network)
    (result : ProcessResult)
    (h_proc : processSegment s.endpointA seg = result) :
    SystemStep s {
      endpointA := result.endpoint
      endpointB := s.endpointB
      network := rest ++ result.segments }
  /-- Deliver a segment from the network to endpoint B. -/
  | deliverToB (s : System) (seg : Segment) (rest : List Segment)
    (h_net : s.network = seg :: rest ∨ seg ∈ s.network)
    (result : ProcessResult)
    (h_proc : processSegment s.endpointB seg = result) :
    SystemStep s {
      endpointA := s.endpointA
      endpointB := result.endpoint
      network := rest ++ result.segments }
  /-- A user call on endpoint A. -/
  | userCallA (s : System) (call : UserCall)
    (result : ProcessResult)
    (h_proc : processUserCall s.endpointA call = result) :
    SystemStep s {
      endpointA := result.endpoint
      endpointB := s.endpointB
      network := s.network ++ result.segments }
  /-- A user call on endpoint B. -/
  | userCallB (s : System) (call : UserCall)
    (result : ProcessResult)
    (h_proc : processUserCall s.endpointB call = result) :
    SystemStep s {
      endpointA := s.endpointA
      endpointB := result.endpoint
      network := s.network ++ result.segments }
  /-- A timeout event on endpoint A. -/
  | timeoutA (s : System) (kind : TimeoutKind)
    (result : ProcessResult)
    (h_proc : processTimeout s.endpointA kind = result) :
    SystemStep s {
      endpointA := result.endpoint
      endpointB := s.endpointB
      network := s.network ++ result.segments }
  /-- A timeout event on endpoint B. -/
  | timeoutB (s : System) (kind : TimeoutKind)
    (result : ProcessResult)
    (h_proc : processTimeout s.endpointB kind = result) :
    SystemStep s {
      endpointA := s.endpointA
      endpointB := result.endpoint
      network := s.network ++ result.segments }
  /-- Segment loss: remove a segment from the network without delivery. -/
  | segmentLoss (s : System) (seg : Segment) (rest : List Segment)
    (h_net : s.network = seg :: rest ∨ seg ∈ s.network) :
    SystemStep s { s with network := rest }
  /-- Segment duplication: copy a segment in the network. -/
  | segmentDup (s : System) (seg : Segment)
    (h_mem : seg ∈ s.network) :
    SystemStep s { s with network := seg :: s.network }

/-- A system trace: zero or more `SystemStep` transitions. -/
inductive SystemTrace : System → System → Prop where
  | refl (s : System) : SystemTrace s s
  | step (s₁ s₂ s₃ : System) : SystemStep s₁ s₂ → SystemTrace s₂ s₃ → SystemTrace s₁ s₃

end Tcp
