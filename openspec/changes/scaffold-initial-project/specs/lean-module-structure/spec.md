## ADDED Requirements

### Requirement: Module Organization
The Lean library SHALL be organized into the following modules under `Tcp/`,
each focused on a single concept from the RFC 793 formalization:

- `SeqNum` -- Modular 32-bit sequence number type and arithmetic
- `Types` -- Port, Socket, Segment header, and TCB structures
- `State` -- TCP connection state enum, event type, and transition function
- `Acceptability` -- Segment and ACK acceptability predicates
- `Handshake` -- Three-way handshake correctness theorems
- `Teardown` -- Connection closing and TIME-WAIT theorems
- `Invariants` -- Safety and data delivery invariant proofs

The root `Tcp.lean` SHALL import all modules so that `import Tcp` provides the
full public API.

#### Scenario: All modules imported from root
- **WHEN** a user writes `import Tcp`
- **THEN** all definitions from SeqNum, Types, State, Acceptability, Handshake, Teardown, and Invariants are available

#### Scenario: Each module typechecks independently
- **WHEN** `lake build` is run
- **THEN** every module under `Tcp/` typechecks without errors or `sorry`

### Requirement: Module Documentation
Every module SHALL begin with a `/-- ... -/` doc comment describing its
purpose, its relationship to RFC 793, and a brief summary of its contents.

#### Scenario: Doc comment present
- **WHEN** any `Tcp/*.lean` file is opened
- **THEN** the first non-blank construct is a module-level doc comment

### Requirement: No Placeholder Code
The scaffold modules SHALL NOT contain placeholder definitions such as
`def hello := "world"`. Each module SHALL contain only its doc comment and
namespace declaration until real definitions are added.

#### Scenario: Clean scaffold
- **WHEN** the scaffold is complete
- **THEN** `Tcp/Basic.lean` no longer exists
- **THEN** no module contains `sorry` or trivial placeholder definitions
