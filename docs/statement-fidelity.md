# Statement Fidelity Audit (`zero-error-torus-frontier` v1.0.0)

This audit verifies **literal 1-to-1 correspondence** between every mathematical theorem stated in [`paper/main.tex`](../paper/main.tex), [`CLAIMS.md`](../CLAIMS.md), and [`README.md`](../README.md) and its formal type signature in [`lean/Challenge.lean`](../lean/Challenge.lean) and [`lean/Solution.lean`](../lean/Solution.lean).

## Axiom Footprint Verification
All 32 exported declarations audited in [`results/lean_axioms.txt`](../results/lean_axioms.txt) depend strictly on subsets of `{propext, Classical.choice, Quot.sound}`:
- `sorryAx`: **0 occurrences** across all proved modules (`PalomarChallenge.lean` is the sole intentional target stub, excluded from `defaultTargets`).
- `Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`): **0 occurrences**.
- Custom `axiom` declarations: **0 occurrences**.

## Theorem-by-Theorem Fidelity Matrix

| ID | Paper Theorem Statement | Lean Formal Type (`Challenge.lean`) | Exact Match Notes |
|---|---|---|---|
| **T1a** | $n^2$-to-1 lift for $H_{\mathrm{BPZ}}$ ($n \ge 9$) and $H^*$ ($n \ge 15$) | `T1aStmt` (`t1a_coset_quotient_compression`) | Exact threshold $n \ge 9$ / $n \ge 15$; produces explicit `HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n))`. |
| **T1b** | Quotient ceilings $\lfloor n\lfloor n/4\rfloor/4\rfloor$ ($n \ge 4$) and $\lfloor n\lfloor n/8\rfloor/2\rfloor$ ($n \ge 8$) | `T1bStmt` (`t1b_exact_quotient_ceilings`) | Exact `AlphaLe` universal over all $n \ge 4$ / $n \ge 8$. |
| **T1c** | $H_{\mathrm{BPZ}}$ unit-shift obstruction ($n \ge 5$) vs. $H^*$ privacy & $45 < 49$ ball ($n \ge 15$) | `T1cStmt` (`t1c_intracoset_obstruction_and_hstar_flexibility`) | Proves concrete `∃ h ∈ H_BPZ \ {0}` conflict AND universal non-conflict + exact ball cardinality $45 < 49$. |
| **T1d** | Helical $H_{\mathrm{BPZ}}$ exact ceiling for $m \ge 5$, $m \equiv 0, 1 \pmod 4$ | `T1dStmt` (`t1d_infinite_helical_hbpz_family`) | Exact universal quantification over all $m \ge 5$ with `m % 4 = 0 ∨ m % 4 = 1`. |
| **T1e** | $H^*$ exact ceiling for $k \ge 3$ + $n^2$-port `RichPortSystem` for odd $k \ge 3$ | `T1eStmt` (`t1e_infinite_hstar_family_and_ports`) | Proves both universal ceiling AND `Nonempty (RichPortSystem ...)` with exact `(nB, nN, nA, nD, d)` equalities. |
| **T1f** | Baumert locally-injective pullback $C_{p+2}^{\boxtimes d} \to C_p^{\boxtimes d}$ ($p \ge 5$) + factored cardinality | `T1fStmt` (`t1f_baumert_pullback_homomorphism`) | Universal over all $p \ge 5$ and $d \ge 1$, plus exact factored sum formula. |
| **T2a** | $\exists M, \alpha(C_{25}^{\boxtimes 144}) \ge M \land 12344196091426841^{144} \le M \cdot (10^{15})^{144}$ | `T2aStmt` (`t2a_c25_world_record`) | Exact integer power inequality, tight to final ULP (verified by mutation test in `tests/test_all.py`). |
| **T2b** | $\exists M, \alpha(C_{27}^{\boxtimes 2048}) \ge M \land 13319390984674515^{2048} \le M \cdot (10^{15})^{2048}$ | `T2bStmt` (`t2b_c27_world_record`) | Exact integer power inequality, tight to final ULP. |
| **T2c** | $\alpha(C_{29}^{\boxtimes 4}) \ge 42050 \land 14319949949077991^4 \le 42050 \cdot (10^{15})^4$ | `T2cStmt` (`t2c_c29_world_record`) | Exact integer power inequality, tight to final ULP. |
| **T2d** | $\exists M, \alpha(C_{31}^{\boxtimes 2048}) \ge M \land 15308776193986504^{2048} \le M \cdot (10^{15})^{2048}$ | `T2dStmt` (`t2d_c31_world_record`) | Exact integer power inequality, tight to final ULP. |
| **T3a** | Induced $C_5 \subset G_7$, $\alpha(G_7) \ge 3$, $\forall d, \alpha(G_7^{\boxtimes d}) \le 3^d$ | `T3aStmt` (`t3a_g7_induced_c5_and_exact_capacity`) | Exact bidirectional induced isomorphism + clique cover upper bound. |
| **T3b** | Weighted fractional-clique-cover barrier $D^k \sum_{x \in C} \prod w(x_t) \le U^k$ | `T3bStmt` (`t3b_weighted_fractional_clique_barrier`) | Universal over any graph $G$, weights $w$, clique family, and power $k$. |
| **T3c** | Multi-alphabet two-sided heterogeneous composition + pure-kernel admissibility of `T2a, T3c, T3e, C4a, C4b` | `T3cStmt` (`t3c_heterogeneous_composition_and_tables`) | Polymorphic over distinct graphs $G_1, G_2$ and alphabets $\Sigma_1, \Sigma_2, \Sigma'$. |
| **T4a** | Haemers matrix-rank bound $\forall d, \alpha(G^{\boxtimes d}) \le r^d$ over any `SimpleField F` | `T4aStmt` (`t4a_haemers_rank_theorem`) | Universal over arbitrary `SimpleField F`, graph $G$, and factorization $M = L R$. |
| **T4b** | Exact integer orthogonal-handle sandwich $|I| \cdot s^d \le (H D)^d$ | `T4bStmt` (`t4b_integer_orthogonal_handle_sandwich`) | Pure $\mathbb{Z}$ formulation avoiding real-analysis axioms. |
| **T4c** | $\alpha(C_5^{\boxtimes 2}) \ge 5 \land \forall d, \forall I, |I|^2 \le 5^d$ | `T4cStmt` (`t4c_lovasz_pentagon_theorem`) | Exact integer-square inequality equivalent to $\Theta(C_5) = \sqrt{5}$. |
| **T4d** | $\alpha(G_{27}^{\boxtimes d}) \le 3^d$, $\alpha(\overline{G_{27}}^{\boxtimes d}) \le 7^d$, $\alpha(G_{27} \boxtimes \overline{G_{27}}) \ge 27$ | `T4dStmt` (`t4d_haemers_schlafli_paradox`) | Exact match to Haemers (1979) Theorems 1–2 ($27 > 3 \times 7 = 21$). |

## Non-Vacuity & Negative Checks
- `ZeroErrorFrontier/NonVacuity.lean`: 7 theorems instantiating all hypotheses with concrete non-trivial graphs and port systems.
- `ZeroErrorFrontier/AdversarialTests.lean`: 7 negative theorems proving invalid packings, colliding handles, and unit-step $H_{\mathrm{BPZ}}$ shifts are formally impossible.
