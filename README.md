# Formal Verification of TCP (RFC 793)

A publication-quality formal verification of the Transmission Control Protocol
as specified in RFC 793, producing machine-checked proofs in Lean 4 and an
accompanying whitepaper.

## Prerequisites

- [Lean 4](https://lean-lang.org/) (v4.28.0 or compatible)
- [Lake](https://github.com/leanprover/lake) (bundled with Lean)
- A LaTeX distribution (e.g., TeX Live, MacTeX) for building the whitepaper

## Building

### Lean Library

```sh
lake build
```

This typechecks all modules. If it succeeds, all theorems hold.

### Whitepaper

```sh
pdflatex whitepaper.tex
bibtex whitepaper
pdflatex whitepaper.tex
pdflatex whitepaper.tex
```

## Module Structure

| Module | Description |
|---|---|
| `Tcp.SeqNum` | Modular 32-bit sequence number arithmetic |
| `Tcp.Types` | Port, Socket, Segment header, TCB structures |
| `Tcp.State` | Connection state enum, events, transition function |
| `Tcp.Acceptability` | Segment and ACK acceptability predicates |
| `Tcp.Handshake` | Three-way handshake correctness theorems |
| `Tcp.Teardown` | Connection closing and TIME-WAIT theorems |
| `Tcp.Invariants` | Safety and data delivery invariant proofs |

## License

See repository for license details.
