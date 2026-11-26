# ADR 0002: Chunked 81-Ball Certificates & 28-Digit Monotonic Truncation

- **Status:** Accepted
- **Date:** 2026-11-25
- **Archive ID:** `0TH-2026-016`

## Context
Certifying the Baumert-pullback port systems for $C_{27}$ (31,466 words, 88 ports) and $C_{31}$ (54,913 words, 133 ports) and verifying 2,427-digit integer powers at $p=2048$ naively inside Lean's pure kernel hits default `maxRecDepth` (512) and heartbeat limits unless either `native_decide` or global option overrides are used—both of which degrade kernel auditability.

## Decision
1. **81-ball local membership certification:** Replace explicit 54,913-word lists with $O(1)$ bitmask quotient membership (`inMaskHBPZ4`) plus zero-division explicit-coordinate 81-neighbor scans (`check81Ball4`).
2. **Chunked sorted lists ($\le 16$ per chunk):** Partition sorted port/footprint code lists (`ports27C`, `footA27C`, `footD27C`, `ports31C`, `footA31C`, `footD31C`) with range-pruned lookup (`elemSortedChunks`), capping kernel recursion depth at $\le 65 \ll 512$.
3. **28-digit monotonic fixed-point truncation:** Track rigorous integer lower bounds $L \cdot 10^e \le w(c)$ across each substitution step (`stepLo_tbl`, `stepFinal_code`), proving the printed 15-decimal values as lower bounds in ~20 seconds total (last-digit tightness is checked outside Lean) with zero `native_decide` and zero `maxRecDepth` overrides.

## Consequences
- All four lower-bound certificates ($C_{25}, C_{27}, C_{29}, C_{31}$) verify cleanly in pure kernel reduction across all 6 independent proof checkers. Two of them ($C_{27}$, $C_{31}$) are below 2003 published values and are not records (see `ERRATA.md`).
- Independently cross-checked to exact 80-digit integer arithmetic in `reference/capacity_oracle.py`.
