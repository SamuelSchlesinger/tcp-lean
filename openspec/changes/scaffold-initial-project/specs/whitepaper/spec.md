## ADDED Requirements

### Requirement: Whitepaper Document
The project SHALL include a `whitepaper.tex` LaTeX document at the repository
root, structured to accompany the Lean formalization. The document SHALL
include:

- Title, author, and abstract
- Section stubs corresponding to each Lean module (Introduction, Sequence
  Numbers, Core Types, State Machine, Segment Acceptability, Connection
  Establishment, Connection Teardown, Invariants and Safety Properties)
- A conclusion section
- A bibliography referencing at minimum RFC 793

#### Scenario: LaTeX compiles
- **WHEN** `pdflatex whitepaper.tex && bibtex whitepaper && pdflatex whitepaper.tex && pdflatex whitepaper.tex` is run
- **THEN** `whitepaper.pdf` is produced without errors

#### Scenario: Sections mirror Lean modules
- **WHEN** a reader opens the whitepaper
- **THEN** each major Lean module has a corresponding section in the paper

### Requirement: Bibliography
The project SHALL include a `references.bib` BibTeX file containing at minimum
an entry for RFC 793. Theorem citations in the whitepaper SHALL reference
named Lean theorem identifiers.

#### Scenario: RFC 793 cited
- **WHEN** the bibliography is compiled
- **THEN** RFC 793 appears as a citable reference

### Requirement: Build Artifacts Excluded
The whitepaper PDF and all LaTeX intermediate files SHALL NOT be committed to
version control. They MUST be listed in `.gitignore`.

#### Scenario: Artifacts gitignored
- **WHEN** `pdflatex whitepaper.tex` is run
- **THEN** `git status` shows no new untracked `.pdf`, `.aux`, `.log`, `.out`, `.toc`, `.synctex.gz`, `.bbl`, `.blg`, `.fdb_latexmk`, or `.fls` files
