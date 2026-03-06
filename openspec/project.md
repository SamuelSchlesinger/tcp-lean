# Project Context

## Purpose

A publication-quality formal verification of the Transmission Control Protocol
(TCP) as specified in RFC 793. The project produces two artifacts:

1. A Lean 4 library (`Tcp`) containing definitions, state machine models, and
   machine-checked proofs of correctness properties.
2. A LaTeX whitepaper (`whitepaper.tex` → `whitepaper.pdf`) describing the
   formalization, design decisions, and proved theorems.

The goal is a research artifact suitable for peer-reviewed publication.

## Tech Stack

- **Lean 4** (v4.28.0) — theorem prover and programming language
- **Lake** — Lean build system (configured via `lakefile.toml`)
- **LaTeX** — whitepaper typesetting (`whitepaper.tex`)

## Project Conventions

### Code Style

- Follow **Mathlib conventions**: `camelCase` for definitions and lemmas,
  `PascalCase` for types and structures.
- All definitions, structures, and significant theorems must have **doc
  comments** (`/-- ... -/`). Inline comments where logic is non-obvious.
- Prefer tactic-mode proofs for non-trivial theorems; term-mode is fine for
  simple definitions and straightforward lemmas.
- Keep files focused: one major concept per file (e.g., sequence number
  arithmetic, state machine, handshake proofs).

### Architecture Patterns

The Lean library is organized by concept:

```
Tcp/
  SeqNum.lean        -- Modular 32-bit sequence number arithmetic
  Types.lean         -- Port, Socket, Segment, TCB structures
  State.lean         -- TcpState enum, Event type, transition function
  Acceptability.lean -- Segment/ACK acceptability predicates and lemmas
  Handshake.lean     -- Three-way handshake correctness theorems
  Teardown.lean      -- Connection closing theorems
  Invariants.lean    -- Safety and data delivery properties
```

Each file imports only what it needs. The root `Tcp.lean` re-exports the
public API.

### Testing Strategy

No executable tests. Correctness is established entirely through
**machine-checked proofs**. If a file typechecks, its theorems hold.

The whitepaper serves as the human-readable validation layer, explaining what
each theorem means and why it matters.

### Git Workflow

- Single branch: **`dev`** with direct commits.
- Commit messages should be concise and describe the mathematical content
  (e.g., "Define segment acceptability predicate", "Prove handshake reaches
  ESTABLISHED").
- The whitepaper PDF is a build artifact and must not be committed. LaTeX
  intermediates (`.aux`, `.log`, `.out`, `.toc`, `.synctex.gz`, etc.) must
  also be gitignored.

## Domain Context

The formalization targets **RFC 793** (September 1981), the original TCP
specification. Key concepts from the RFC that drive the formalization:

- **11 connection states**: CLOSED, LISTEN, SYN-SENT, SYN-RECEIVED,
  ESTABLISHED, FIN-WAIT-1, FIN-WAIT-2, CLOSE-WAIT, CLOSING, LAST-ACK,
  TIME-WAIT.
- **Modular sequence number arithmetic**: 32-bit unsigned, mod 2³². The
  comparison relation is not a total order — it is meaningful only within a
  half-space (2³¹ window).
- **Three-way handshake**: SYN → SYN-ACK → ACK for connection establishment.
- **Graceful close**: FIN exchange with TIME-WAIT (2×MSL) to drain old
  segments.
- **Sliding window**: flow control via send/receive windows over sequence
  number space.
- **TCB variables**: SND.UNA, SND.NXT, SND.WND, RCV.NXT, RCV.WND, ISS, IRS.

Later RFCs (congestion control, timestamps, window scaling) are explicitly
**out of scope** for the initial formalization.

## Important Constraints

- All proofs must typecheck with `lake build` — no `sorry` in merged code.
- The whitepaper must stay synchronized with the Lean formalization: theorems
  cited in the paper must correspond to named Lean theorems.
- Stick to RFC 793 only; do not incorporate later TCP extensions.

## External Dependencies

- **Mathlib4** — may be used for general-purpose lemmas (arithmetic, data
  structures) if needed. Prefer self-contained proofs where the Mathlib
  dependency would be heavy.
- No runtime or network dependencies. This is a purely logical artifact.
