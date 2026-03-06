## 1. Project Configuration
- [x] 1.1 Update `.gitignore` with LaTeX build artifacts
- [x] 1.2 Update `README.md` with project description and build instructions

## 2. Lean Module Structure
- [x] 2.1 Create `Tcp/SeqNum.lean` with module doc comment and namespace
- [x] 2.2 Create `Tcp/Types.lean` with module doc comment and namespace
- [x] 2.3 Create `Tcp/State.lean` with module doc comment and namespace
- [x] 2.4 Create `Tcp/Acceptability.lean` with module doc comment and namespace
- [x] 2.5 Create `Tcp/Handshake.lean` with module doc comment and namespace
- [x] 2.6 Create `Tcp/Teardown.lean` with module doc comment and namespace
- [x] 2.7 Create `Tcp/Invariants.lean` with module doc comment and namespace
- [x] 2.8 Remove `Tcp/Basic.lean`
- [x] 2.9 Update `Tcp.lean` to import all new modules

## 3. Whitepaper
- [x] 3.1 Create `whitepaper.tex` with title, abstract, section stubs, and bibliography
- [x] 3.2 Create `references.bib` with RFC 793 entry

## 4. Validation
- [x] 4.1 Verify `lake build` succeeds with all new modules
- [x] 4.2 Verify `pdflatex whitepaper.tex` compiles (or document the build command)
