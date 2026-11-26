# Roadmap

## Completed (`v1.0.0`)

- Zero-Mathlib Lean 4.35.0 formalization of all 4 pillars (Theorems T1a–T4d), 6-kernel verification, Palomar Comparator contract, NonVacuity and AdversarialTests modules.
- Four consecutive new odd-cycle Shannon capacity lower bounds ($C_{25}, C_{27}, C_{29}, C_{31}$) verified without `native_decide`.
- Infinite exact-ceiling packing families for $H_{\mathrm{BPZ}}$ ($n=4m+1$, $m \equiv 0,1 \pmod 4$) and $H^*$ ($n=8k+1$, $k \ge 3$) with infinite $n^2$-port systems for $n=16j+9$.
- Rust stdlib optimizer, C11 zero-warning verifier + fuzz/ASan/UBSan, exact Python oracle + property/differential/mutation tests, AMS-LaTeX white paper + arXiv bundle, and interactive GitHub Pages blueprint explorer.

## Planned Future Directions (`v1.1+`)

1. **Higher-Dimensional $d = 5$ Quotient Compression ($n \ge 33$):** Generalize the 45-ball subgroup discovery to 3D/2D quotient lattices inside $C_n^{\boxtimes 5}$ for odd cycles $33 \le n \le 63$ ($2^5+1 \le n < 2^6+1$).
2. **Non-Quotient Local Repacking of $C_{21}^{\boxtimes 4}$:** Investigate whether breaking $H_{21}$ down to non-periodic local perturbations can exceed $\alpha(C_{21}^{\boxtimes 4}) \ge 11{,}466$ toward Baumert's upper bound $11{,}576$.
3. **New Arity-4/5 Substitution Tables over $G_7$:** Close the gap between the achieved $C_{25}$ bound ($12.344196\dots$) and our certified fractional-clique-cover barrier ($12.373080\dots$) on the 625-port $H^*$ profile.
4. **Formalized Real-Number Shannon Capacity Limit Bridge:** Extend the pure-integer $\alpha(G^{\boxtimes d})$ certificates to a standalone zero-Mathlib Dedekind/Cauchy supremum formulation if requested by downstream Lean libraries.
