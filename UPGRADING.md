# Upgrading Guide

## `v1.0.0` (Initial Public Release — 2026-11-25)

This is the initial release (`v1.0.0`, archive ID `0TH-2026-014`). No breaking upgrades apply.

### Toolchain Compatibility

- **Lean:** `leanprover/lean4:v4.35.0` (pinned in `lean/lean-toolchain`; zero external Lean dependencies).
- **Rust:** `1.94.1` (edition 2021, zero external crates).
- **C:** strict ISO C11 (`-std=c11 -Wall -Wextra -Wpedantic -Werror`).
- **Python:** `3.12+` (stdlib core + `pytest`, `hypothesis`, `matplotlib` for tests and figures).
- **LaTeX:** Tectonic `0.17.0` (`amsart`, `amsmath`, `amssymb`, `amsthm`, `booktabs`, `hyperref`, `graphicx`).
