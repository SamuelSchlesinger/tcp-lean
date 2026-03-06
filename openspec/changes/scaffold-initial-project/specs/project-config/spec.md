## ADDED Requirements

### Requirement: Gitignore Configuration
The `.gitignore` SHALL exclude:

- Lake build artifacts (`/.lake`)
- LaTeX build artifacts (`*.aux`, `*.log`, `*.out`, `*.toc`, `*.synctex.gz`,
  `*.pdf`, `*.bbl`, `*.blg`, `*.fdb_latexmk`, `*.fls`)

#### Scenario: Lake artifacts ignored
- **WHEN** `lake build` is run
- **THEN** the `.lake/` directory does not appear in `git status`

#### Scenario: LaTeX artifacts ignored
- **WHEN** `pdflatex whitepaper.tex` is run
- **THEN** no LaTeX intermediate or output files appear in `git status`

### Requirement: README
The `README.md` SHALL contain:

- Project title and one-paragraph description
- Build prerequisites (Lean 4, LaTeX)
- Build instructions for both the Lean library (`lake build`) and the
  whitepaper
- A brief description of the module structure

#### Scenario: Build instructions present
- **WHEN** a new contributor reads `README.md`
- **THEN** they find step-by-step instructions to build both artifacts
