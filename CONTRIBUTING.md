# Contributing

Thank you for your interest in auditing, reproducing, or extending `zero-error-torus-frontier`.

## Standards for Contributions & Bug Reports

1. **Zero-Mathlib Pure-Kernel Policy:** All Lean 4 modules in `lean/` must compile under `leanprover/lean4:v4.35.0` with `module` headers, zero Mathlib imports, zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms, and axioms strictly within `[propext, Classical.choice, Quot.sound]`.
2. **Multi-Language Parity:** Any change to coset packings, port witnesses, substitution tables, or Schläfli certificates must pass Lean 4, Rust (`cargo test` + `cargo clippy`), C11 (`make -C native test sanitizers`), and Python (`pytest tests/test_all.py`).
3. **Licensing:** Code contributions are licensed under Apache-2.0 (`LICENSE`); documentation and manuscript prose are licensed under CC-BY-4.0 (`LICENSE-DOCS`).
4. **How to Report Improvements or Counterexamples:** Open an issue at <https://github.com/0thernes/zero-error-torus-frontier/issues> with exact reproduction commands and expected vs. observed outputs.
