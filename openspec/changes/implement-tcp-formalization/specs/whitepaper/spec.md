## ADDED Requirements

### Requirement: Whitepaper Content
The whitepaper SHALL contain substantive prose (not just stubs) in every section,
describing:
- **Introduction**: Motivation for formal TCP verification, contributions of
  the paper, positioning relative to prior work
- **Sequence Numbers**: Definition of `SeqNum`, the circular less-than relation,
  and key properties, with reference to RFC 793 §3.3
- **Core Types**: Design choices for `Segment`, `Tcb`, and `TcpState`, with
  reference to RFC 793 §3.1--3.2
- **State Machine**: The two-endpoint system model, event processing
  architecture, and how RFC 793 §3.9 maps to the Lean definitions
- **Segment Acceptability**: The 4-case predicate, ACK acceptability, and
  proved lemmas
- **Connection Establishment**: Statement and proof sketch of handshake
  theorems (normal, simultaneous, old-duplicate recovery, half-open detection)
- **Connection Teardown**: Statement and proof sketch of close theorems
  (normal, simultaneous, TIME-WAIT)
- **Invariants and Safety Properties**: Statement and proof sketch of each
  safety invariant and data delivery property
- **Conclusion**: Summary of results, limitations, and directions for future work

#### Scenario: No empty sections
- **WHEN** the whitepaper PDF is compiled
- **THEN** every section contains at least one paragraph of substantive content

### Requirement: Theorem Cross-References
Every theorem discussed in the whitepaper SHALL reference the corresponding
named Lean theorem identifier (e.g., `Tcp.Handshake.threeWayHandshakeCorrect`).
Conversely, every significant Lean theorem SHALL have a doc comment citing the
relevant RFC 793 section.

#### Scenario: Lean theorem referenced in paper
- **WHEN** the whitepaper states a theorem about handshake correctness
- **THEN** it includes the Lean identifier for the corresponding machine-checked proof

#### Scenario: RFC cited in Lean doc comment
- **WHEN** a theorem in `Tcp/Handshake.lean` is defined
- **THEN** its doc comment cites RFC 793 §3.4

### Requirement: Whitepaper Compiles
The whitepaper SHALL compile without errors using the standard LaTeX build
pipeline: `pdflatex`, `bibtex`, `pdflatex`, `pdflatex`.

#### Scenario: Clean build
- **WHEN** the full LaTeX build pipeline is run
- **THEN** `whitepaper.pdf` is produced without errors or undefined references
