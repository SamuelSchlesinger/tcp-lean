# Change: Scaffold initial project structure

## Why
The repository currently contains only a placeholder `Tcp/Basic.lean` with
`def hello := "world"`. To begin the formalization of RFC 793, we need the
foundational Lean module structure, a LaTeX whitepaper skeleton, and proper
build/ignore configuration in place before any definitions or proofs can be
written.

## What Changes
- **Lean modules**: Create the seven-file module structure defined in
  `project.md` (`SeqNum`, `Types`, `State`, `Acceptability`, `Handshake`,
  `Teardown`, `Invariants`), each with doc comments explaining its purpose and
  placeholder `sorry`-free scaffolding. Remove the placeholder `Basic.lean`.
  Update `Tcp.lean` to import all modules.
- **Whitepaper**: Create `whitepaper.tex` with a minimal but well-structured
  LaTeX document (title, abstract, section stubs mirroring the Lean modules,
  bibliography).
- **Project config**: Update `.gitignore` to exclude LaTeX build artifacts
  (`*.aux`, `*.log`, `*.out`, `*.toc`, `*.synctex.gz`, `*.pdf`, `*.bbl`,
  `*.blg`, `*.fdb_latexmk`, `*.fls`). Update `README.md` with a project
  description and build instructions.

## Impact
- Affected specs: `lean-module-structure`, `whitepaper`, `project-config`
  (all new)
- Affected code: `Tcp.lean`, `Tcp/Basic.lean` (removed), `Tcp/*.lean` (new),
  `whitepaper.tex` (new), `.gitignore`, `README.md`
