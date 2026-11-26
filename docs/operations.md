# Operations & Maintenance Runbook (`zero-error-torus-frontier` v1.0.0)

## Local Verification Commands

Run the full verification stack locally via `just all` or individually:

1. **Lean 4.35.0 formal build + axiom audit + kernel checkers:**
   ```bash
   cd lean
   lake build
   lake build PalomarChallenge
   lake env lean VerifyAxioms.lean
   lake env leanchecker --fresh Solution
   lake env leanchecker-paranoid --fresh Solution
   ```
   On Linux with `bubblewrap` installed, run the full 6-kernel paranoid check:
   ```bash
   cd lean
   lake check --paranoid
   lake comparator --config comparator.json --paranoid
   ```
2. **Rust verifier:**
   ```bash
   cd rust
   cargo clippy --all-targets -- -D warnings
   cargo test --release
   cargo run --release -- --verify-all
   ```
3. **ISO C11 verifier (Linux/macOS with GCC or Clang):**
   ```bash
   cd native
   make clean && make test && make sanitize && make fuzz
   ```
4. **Python oracle, unit/property/differential/mutation tests & anti-drift audits:**
   ```bash
   pytest -v tests/test_all.py
   python examples/quickstart_demo.py
   python scripts/check_readme_axioms.py
   python scripts/check_citations.py --live
   ruff check python/ reference/ scripts/ tests/ examples/
   mypy --ignore-missing-imports python/ reference/ scripts/ tests/ examples/
   ```
5. **Figures, Blueprint, Manuscript PDF & Clean-Room arXiv Check:**
   ```bash
   python scripts/generate_figures.py
   python scripts/build_blueprint.py
   tectonic -X compile paper/main.tex --outdir paper/build --keep-logs
   ```
6. **Build Standard v1.2.0 Repository Audit:**
   ```powershell
   pwsh -NoProfile -File scripts/Audit-Repo.ps1 -Path .
   ```
   or on Linux/macOS:
   ```bash
   bash scripts/audit-repo.sh .
   ```

## Offsite Backup, Git Bundle & Software Heritage Mirror

To preserve an offline verifiable mirror of the complete Git history and frozen artifacts:
```bash
# Create a self-contained offline Git bundle mirror
git bundle create zero-error-torus-frontier-v1.0.0.bundle --all
git bundle verify zero-error-torus-frontier-v1.0.0.bundle
```
In addition to GitHub, this repository is mirrored permanently via:
1. **Software Heritage Archive** (Save Code Now snapshot triggered at release `v1.0.0`).
2. **Master Research Archive (`0thernes-research-archive`)** as Tier I entry `0TH-2026-014` with pinned submodule commit, frozen PDF copy, and SHA-256 checksum manifest.

## Regenerating Checksums & `llms-full.txt`
Whenever any frozen artifact changes, regenerate `MANIFEST.sha256`, `data/MANIFEST.sha256`, and `llms-full.txt` before tagging a release.
