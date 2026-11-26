# SPDX-License-Identifier: Apache-2.0
set shell := ["bash", "-cu"]

default: verify

# Build and strictly audit all Lean 4.35.0 proofs (zero Mathlib, zero native_decide)
lean:
    cd lean && lake build && lake build PalomarChallenge && lake env lean VerifyAxioms.lean > ../results/lean_axioms_local.txt
    ! grep -E "sorryAx|_native|Lean\.ofReduceBool|Lean\.trustCompiler" results/lean_axioms_local.txt
    cd lean && lake env leanchecker --fresh Solution && lake env leanchecker-paranoid --fresh Solution

# Build and test stdlib-only Rust engine
rust:
    cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --verify-all

# Build and test zero-warning ISO C11 independent verifier (+ sanitizers & fuzz)
native:
    make -C native clean test sanitize fuzz

# Run Python exact oracle, pytest, property, differential, mutation, axiom-drift & citation checks
python:
    PYTHONPATH=python python examples/quickstart_demo.py
    PYTHONPATH=python pytest tests/test_all.py -v
    python scripts/check_readme_axioms.py
    python scripts/check_citations.py
    python scripts/build_blueprint.py

# Regenerate vector PDF/PNG figures and compile AMS-LaTeX white paper with Tectonic
paper:
    PYTHONPATH=python python scripts/generate_figures.py
    mkdir -p paper/build
    tectonic -X compile paper/main.tex --outdir paper/build --keep-logs

# End-to-end clean-clone reproduction entry point (Build Standard B01)
reproduce: lean rust python paper
    sha256sum -c data/MANIFEST.sha256
    sha256sum -c MANIFEST.sha256

# Full verification ladder
verify: lean rust native python paper
