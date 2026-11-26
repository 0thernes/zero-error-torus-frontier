# ADR 0003: Dual Licensing, Direct-to-Main Provenance & Standalone Provenance

- **Status:** Accepted
- **Date:** 2026-11-25
- **Archive ID:** `0TH-2026-016`

## Context
Academic mathematical software repositories combine executable verification code (Lean, Rust, C11, Python) with scholarly writing and figures (`paper/`, `docs/`, `dist/`), and require clean archival provenance without workflow friction.

## Decision
- Code artifacts are licensed under `Apache-2.0` (`LICENSE`); documentation, manuscript, and figures under `CC-BY-4.0` (`LICENSE-DOCS`), declared machine-readably in `REUSE.toml`.
- Author identity is strictly `Alexander Stephen Donahue` (Independent Researcher, ORCID `0009-0006-8168-9648`).
- Commits and releases push directly to `main` with informational CI (no branch protection or PR friction), SHA-256 checksum manifests (`MANIFEST.sha256`, `data/MANIFEST.sha256`), GitHub Release SLSA build provenance attestation, Software Heritage Save Code Now archival, and Tier I registration (`0TH-2026-016`) in `0thernes-research-archive`.

## Consequences
- Full SPDX/REUSE clarity for both software reuse and academic citation.
- End-to-end cryptographic traceability from Lean proof terms and frozen PDF to public GitHub Release and Software Heritage snapshot.
