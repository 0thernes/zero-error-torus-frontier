# Security Policy

## Scope

`zero-error-torus-frontier` is an offline mathematical formalization, multi-language computational verifier (Lean 4.35.0, Rust, C11, Python), and AMS-LaTeX manuscript repository. It runs no network daemons, holds no user credentials, and processes no untrusted network input.

## Reporting a Vulnerability or Soundness Issue

- **Proof soundness / axiom / kernel discrepancies** (e.g., an unexpected axiom, a `native_decide` slip, a specification mismatch, or a counterexample to any theorem claim): open a public GitHub issue using the `bug.yml` template or email `0_0@0thernes.art` with `[SOUNDNESS]` in the subject line.
- **Memory safety or parser bugs in `native/` (C11) or `rust/`**: email `0_0@0thernes.art` with `[SECURITY]` in the subject line, or open a public issue if no exploit impact exists.
- **Response target:** acknowledgement within 72 hours; triage and public errata update in `ERRATA.md` within 7 days.

## Supply-Chain & TCB Posture

- Zero Mathlib dependency (`lean/lake-manifest.json` has `packages: []`).
- Six-kernel verification on Ubuntu CI (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche`, `con-ron`, `nanoda_bin` + `lake comparator --paranoid`).
- C11 verifier compiled with `-std=c11 -Wall -Wextra -Wpedantic -Werror` and tested under AddressSanitizer + UndefinedBehaviorSanitizer + standalone fuzzing.
- Frozen artifacts (`dist/*.pdf`, `dist/arxiv_submission.tar.gz`, `MANIFEST.sha256`) attested via GitHub Actions SLSA provenance (`actions/attest-build-provenance`).
