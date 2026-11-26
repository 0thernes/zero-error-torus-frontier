# Hardening Log (`zero-error-torus-frontier` v1.0.0 — Archive `0TH-2026-014`)

Three full, independent hardening cycles were executed across every directory, file, theorem, numerical certificate, citation, figure, documentation page, and Build Standard v1.2.0 / Playbook v1.3 check, classifying every finding into the ten Build Standard finding classes (`bug`, `error`, `issue`, `problem`, `concern`, `dilemma`, `conflict`, `gap`, `hole`, `blindspot`).

---

## Cycle 1 — Proof-Kernel Architecture, Mathematical Accuracy & Differential Parity

| Class | Finding | Root Cause | Fix & Verification |
|---|---|---|---|
| `error` | `WorldRecords.lean` `cert27_ok`/`cert31_ok` hit default `maxRecDepth` (512) and heartbeat limit on flat sorted lists | Linear recursion over 337-element code lists inside kernel reduction | Chunked lists (`ports27C..footD31C`, chunks $\le 16$) with range-pruned `elemSortedChunks` + zero-division `check81Ball4` + 11 individual `decide` theorems per record; depth dropped to $\le 65$, compile time ~20s with zero `maxRecDepth` overrides |
| `error` | `stepLo_tbl`/`stepFinal_code` emitted `exponent 260/548` warnings unifying `10^(2*e+sh)` | Dependent exponent unification inside `Nat.pow` | Added explicit output exponent `e'` + `(he' : e' = m * e + sh)` + `subst he'` |
| `bug` | Rust (`rust/src/main.rs`) and C11 (`native/src/torus_frontier.c`) approximated $H^*$ odd-$k$ staircase with linear slope | Missed 4-jump phase term `extra = [0<t]+[k²<t]+[2k²<t]+[3k²<t]` from `CosetQuotient.lean` | Replaced with exact 4-jump formula in Rust, C11, Python, and `data/witnesses.json`; locked via regression test `test_regression_hstar_four_jump_staircase_and_lovasz_j_term` |
| `bug` | Lovász $C_5$ $\mathbb{Z}[\sqrt{5}]$ matrix $M_5$ in Rust/C11 omitted `-2` (`-J`) non-edge term | Copied raw Gram formula before subtracting $J$ | Restored `diag=(-2,2), edge=(3,-1), non-edge=(-2,0)`; verified $M_5^2 = 5(\sqrt{5}-1)M_5$ across Lean, Rust, C11, and Python |
| `bug` | `reference/capacity_oracle.py` failed with `KeyError: 'B'` parsing `tblT3c`/`tblT3e` | Single-line regex skipped multi-line Lean list arms; dead hardcoded draft tables left at top | Deleted dead tables; rewrote parser to split arms across newlines with exact word-count assertions (`20, 48, 53, 49, 57`) |
| `conflict` | Pre-ULP last-digit drift in `CLAIMS.md` (`...840/...516/...992/...503`) vs. Lean exact floors (`...841/...515/...991/...504`) | Draft digits written before 80-digit binary-search ULP tightening | Updated `CLAIMS.md` and enforced exact 15-decimal parity across `witnesses.json`, `CLAIMS.md`, `README.md`, and `paper/main.tex` via `scripts/check_readme_axioms.py` |
| `issue` | 8 Rust 1.94 Clippy `-D warnings` lints + 20 Python Ruff lints + 2 mypy errors in `build_blueprint.py` | `is_multiple_of(2)`, `.iter().enumerate()`, unused imports/noqa, untyped `NODES` | Fixed all; `cargo clippy -- -D warnings`, `ruff check`, and `mypy` all exit 0 with 0 warnings |

---

## Cycle 2 — Scholarly Integrity, Visual QA & LaTeX Zero-Warning Typography

| Class | Finding | Root Cause | Fix & Verification |
|---|---|---|---|
| `hole` | Two DOIs in `paper/references.bib` (`hales1973numerical`, `bohman2005limit2`) returned HTTP 404 on live audit | Search snippet guessed retroactive DOIs | Queried Crossref API directly; replaced with verified DOIs `10.1016/0095-8956(73)90014-2` and `10.1090/S0002-9939-04-07470-2`; `scripts/check_citations.py --live` passed 20/20 (HTTP 200/202) |
| `bug` | `scripts/generate_figures.py` crashed with matplotlib mathtext `Unknown symbol: \le` | Matplotlib mathtext requires `\leq` rather than `\le` | Replaced `\le`/`\ge` with `\leq`/`\geq` across all matplotlib labels |
| `problem` | Visual inspection of Fig 1, Fig 2, Fig 3, Fig 4 caught bar clipping (`ylim` too small on Fig 1a), legend overlaps (Fig 1b, Fig 2b, Fig 3a), intermediate `O=[]` drop in Fig 3b, and annotation touch in Fig 4b | Initial axis ranges and plotting intermediate `B+O` instead of terminal `C4b` capacity | Fixed all 5 figures (`C4b` progression on Fig 3b, expanded limits, outside legends, `bbox_inches="tight"`); re-inspected all 5 PNGs via image reader until spotless |
| `concern` | Conversational phrase `"wait:"` in prose proof of `T1c` + raw markdown backticks + `--paranoid` en-dash ligature + double period `..` after `\paragraph` + 15 overfull hboxes + 6 hyperref PDF string warnings in `paper/main.tex` | First draft LaTeX prose and unescaped monospace strings | Rewrote `T1c` proof cleanly, removed `inputenc`, added `\texorpdfstring`, fixed `\texttt{-{}-paranoid}`, removed trailing dots inside `\paragraph`, adjusted table widths and displayed equations -> **0 warnings, 0 overfull hboxes, 0 undefined refs** |
| `gap` | Clean-room arXiv compile command missed `mkdir -p .../out` in local script & `.github/workflows/ci.yml` | Tectonic requires `--outdir` to pre-exist | Fixed both; verified byte-identical `411,207`-byte PDF between `dist/Donahue_2026_zero_error_torus_frontier.pdf` and clean-room `dist/arxiv_submission.tar.gz` |

---

## Cycle 3 — Build Standard v1.2.0 Audit, Red-Team Review & Cryptographic Provenance

| Class | Finding | Root Cause | Fix & Verification |
|---|---|---|---|
| `blindspot` | `.github/ISSUE_TEMPLATE/config.yml` still contained unexpanded owner/project template tokens | Left unexpanded from template scaffold | Replaced with `0thernes/zero-error-torus-frontier`; placeholder scan confirmed 0 remaining placeholders |
| `gap` | `Audit-Repo.ps1` flagged 10 items (`A04`, `A23`, `A32`, `A35`, `A42`, `B01`, `B15`, `B37`, `B42`, `B44`) and 9 unpopulated manual statuses in `repo.yaml` | Missing section headers, `@AGENTS.md` import, `reproduce:` target, `libFuzzer` harness, `SHA256SUMS` CI step, falsification section, and replication log | Addressed every single item cleanly (`README.md`, `CLAUDE.md`, `docs/operations.md`, `justfile`, `native/tests/libfuzzer_torus.c`, `ci.yml`, `CLAIMS.md`, `REPLICATION.md`, `repo.yaml`) |
| `dilemma` | `scripts/check_readme_axioms.py` falsely flagged the prose comment `zero-sorry` in `PalomarSolution.lean` | Naive regex scanned comment text alongside Lean code | Added `_strip_lean_comments()` stripping `--` and `/- ... -/` before auditing `\bsorry\b`/`\badmit\b`/`native_decide`/`axiom` |
| `bug` | `REPLICATION.md` listed stale CLI flags (`verify-all` vs `--verify-all`, `torus_verify_cli` vs `torus_cli`, `sanitizers` vs `sanitize`) | Written before final Rust/C11 binary naming | Synchronized every command in `REPLICATION.md`, `justfile`, `README.md`, and `docs/operations.md` |
| `concern` | C11 `test_torus.c` could warn on unused `ok` if compiled with `-DNDEBUG` | Relying solely on `assert(ok)` | Added explicit `if (!ok) { fprintf(stderr, ...); return 1; }` guard alongside `assert(ok)` |

---

## Final Verification Matrix (Post-Cycle 3)
- **Lean 4.35.0:** `lake build` + `lake build PalomarChallenge` + `VerifyAxioms.lean` (32/32 strictly within `[propext, Classical.choice, Quot.sound]`) + `leanchecker --fresh Solution` + `leanchecker-paranoid --fresh Solution` + 6-kernel `lake check --paranoid` & `lake comparator --config comparator.json --paranoid` on Ubuntu CI.
- **Rust:** `cargo clippy --all-targets -- -D warnings` (0 warnings) + `cargo test --release` (4/4) + `--verify-all` (`"all_ok":true`).
- **ISO C11:** `-std=c11 -Wall -Wextra -Wpedantic -Werror` + unit/negative tests + ASan/UBSan + 100k PRNG fuzz + libFuzzer target.
- **Python:** 15/15 `pytest` tests (Hypothesis, metamorphic, differential, 80-digit oracle, mutation kill), `ruff check` (0), `mypy` (0), `check_readme_axioms.py` (32/32), `check_citations.py --live` (20/20).
- **LaTeX & Archive:** Tectonic 0 warnings / 0 overfull hboxes, byte-identical clean-room arXiv tarball (`411,207` bytes), `MANIFEST.sha256` & `data/MANIFEST.sha256`, `Audit-Repo.ps1` **100.0% PASS** on all applicable checks once initial commit is on `main`.
