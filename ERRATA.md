# Errata

## Policy

Any mathematical error, specification gap, citation correction, or numerical revision discovered after release will be logged permanently in this file with:
1. Date and version affected.
2. Exact theorem / claim / table reference.
3. Root cause and corrected statement or proof commit SHA.
4. Impact on downstream bounds in `CLAIMS.md` and `paper/main.tex`.

## 2026-11-26 statement audit

Version affected: `v1.0.0` (released 2026-11-25), audited at commit `af343aaa1701637e23733ac0abd7a8f9b2e22b60`. Audit log: <https://github.com/0thernes/0thernes-research-archive/blob/main/docs/reviews/2026-11-26-statement-audit.md>.

The audit rebuilt the Lean library at the pinned commit (`lake build` passed), confirmed that all 32 audited declarations use only `propext`, `Classical.choice` and `Quot.sound`, and found the six-kernel CI run for that commit successful. None of the items below invalidates a Lean proof. They concern what the prose claims about the proved statements and about the literature.

`README.md`, `CLAIMS.md`, `LIMITATIONS.md`, `CITATION.cff`, `lean/formalization.yaml` and the Markdown files under `docs/` were corrected on 2026-11-26. The frozen paper (`paper/main.tex`, `dist/Donahue_2026_zero_error_torus_frontier.pdf`, `dist/arxiv_submission.tar.gz`) and the Lean sources were not changed in this pass. The corrections below apply to them.

### Paper (`paper/main.tex` and the frozen PDF)

1. **"Four new world records" (abstract, `main.tex`:62; Section "Pillar II" title, :250; :252; Theorem T2a–T2d title, :254; Table 2 caption, :275; Figure caption, :293).**
   - What is wrong: two of the four bounds are not records. Codenotti, Gerace and Resta, *Some remarks on the Shannon capacity of odd cycles*, Ars Combinatoria 66 (2003) 243–257, Table 1, lists $\alpha(C_{27}^{\boxtimes 4}) \ge 31522$ and $\alpha(C_{31}^{\boxtimes 4}) \ge 54934$, i.e. $13.324577316143$ and $15.309475277725$, above our $13.319390984674515$ and $15.308776193986504$. Our fourth-power bases 31466 and 54913 are also below these values. The paper does not cite this work.
   - Correction: "four machine-checked lower bounds; those for $C_{25}$ and $C_{29}$ exceed the largest published values found (Codenotti–Gerace–Resta 2003: $23125^{1/4}$, $42017^{1/4}$), those for $C_{27}$ and $C_{31}$ are below the values in the same table ($31522^{1/4}$, $54934^{1/4}$)". Add the 2003 paper to the bibliography.
   - Affects a theorem statement: no. The Lean inequalities are unchanged; only the attribute "record" and the theorem title are wrong.

2. **Gap statement (`main.tex`:86).**
   - What is wrong: "the best known lower bounds in the literature remained the 55-year-old three-dimensional Baumert–Hales packings" is false. CGR 2003, Table 1, gives better four-dimensional values for $n = 25, 27, 29, 31$ (23125, 31522, 42017, 54934).
   - Correction: "for odd $n \ge 25$ the largest published values we are aware of are those of Codenotti, Gerace and Resta (2003, Table 1)".
   - Affects a theorem statement: no.

3. **Table 2 (`main.tex`:275–285) and the matching README table.**
   - What is wrong: (a) the baseline column uses third-power values; the right comparison is the $d=4$ column of CGR 2003, Table 1. (b) The net gains are therefore wrong: against CGR 2003 they are $+0.012567519$ ($C_{25}$, stated $+0.013136$), $-0.005186$ ($C_{27}$), $+0.002810330$ ($C_{29}$, stated $+0.015399$), $-0.000699$ ($C_{31}$). (c) The third-power values $2927$ ($C_{29}$) and $3575$ ($C_{31}$) disagree with CGR's $2929$ and $3580$; arXiv:2506.14654, Theorem 1.7, gives $3576$ for $C_{31}$. (d) The Lovász values for $C_{27}, C_{29}, C_{31}$ are printed as $13.454185, 14.457351, 15.460110$; $n\cos(\pi/n)/(1+\cos(\pi/n))$ gives $13.454204, 14.457375, 15.460135$. (e) The $C_{25}$ "$d=4$ base" $23125 = 37 \cdot 25^2$ is exactly the 2003 table entry; $23125^{1/4} = 12.3316285728$, not $12.3316289$ (paper) or $12.3316288890$ (README).
   - Correction: replace the baseline column by the CGR 2003 $d=4$ values with locators, recompute the differences as above, correct the $\vartheta$ decimals, and state that 23125 for $C_{25}^{\boxtimes 4}$ was known.
   - Affects a theorem statement: no.

4. **Last-digit tightness (`main.tex`:270).**
   - What is wrong: "Every 15-decimal floor is tight to the last unit in the last place" is presented inside Theorem T2 but is not a Lean statement. Lean proves only the lower inequality. The audit confirmed tightness independently for $C_{29}$ only.
   - Correction: move the sentence out of the theorem and say that tightness is a computation outside Lean.
   - Affects a theorem statement: yes (the prose theorem asserts more than Lean proves).

5. **"Resolves Open Problem #2 of Tandon" (abstract, `main.tex`:67; :82; gap (3), :88; :355; Theorem T3c title, :357).**
   - What is wrong: Tandon, *Strengthening Recursive Constructions for Zero-Error Shannon Capacity*, arXiv:2608.30273v1 (2026, preprint), has no numbered open problem and does not use the words "multi-alphabet" or "heterogeneous composition". Its Section 5 mentions, as a direction for future work, a two-sided extension of its Theorem 1 (a product theorem for Gao gadgets with profile formulas); Remark 3 leaves it to future work. Theorem T3c takes "separated in at least one coordinate" as a hypothesis and concludes that product blocks form a realisation; it derives no Gao gadget, compatibility condition or profile formula. The same product construction and size formula are Tandon's Definition 6 and Proposition 1, and `Realisation.multiSubst` / `w_multiSubst` in the Buys–Polak–Zuiddam Lean repository (`ShannonBounds/Layered.lean`). The phrase "peer-literature" is also wrong: the preprint has no journal reference.
   - Correction: "T3c is a two-alphabet, two-graph form of the BPZ combining rule (Tandon, arXiv:2608.30273, Proposition 1), plus kernel-checked admissibility of five BPZ tables. The two-sided extension of Tandon's Theorem 1 mentioned in his concluding section is not addressed." At :82, replace "posing the problem of general multi-alphabet heterogeneous composition" by "and mentions, as a direction for future work, a two-sided extension of his heterogeneous product theorem".
   - Affects a theorem statement: no. The Lean statement matches the paper's own Theorem T3c; only the claim that it resolves a published problem is wrong.

6. **$G_7$ and the weighted barrier (abstract, `main.tex`:67; Section "Pillar III").**
   - What is wrong: "$G_7$ contains an induced chordless $C_5$, satisfies $\Theta(G_7) = 3$" suggests the 5-cycle drives the bound. The upper bound is proved by the 3-clique cover $\{B,N\}, \{A,V\}, \{D,O,H\}$; the 5-cycle is a separate conjunct. "Sharp weighted fractional-clique-cover barrier ($46875/2$)": Lean proves an upper bound only; optimality is not proved.
   - Correction: "$\alpha(G_7) \ge 3$ and $\alpha(G_7^{\boxtimes d}) \le 3^d$ by a 3-clique cover (so $\Theta(G_7) = 3$), and $G_7$ contains an induced 5-cycle"; replace "sharp" by "an upper bound of".
   - Affects a theorem statement: no.

7. **Priority and naming for T4c/T4d (abstract, `main.tex`:68; :89; Theorem T4d title, :428; Figure 5 caption, :452).**
   - What is wrong: "the first zero-Mathlib, six-kernel verified proof" rests on no documented priority search. "Paradox" is not the usual name of Haemers's result. "$\Theta(C_5) = \sqrt{5}$" is a consequence outside Lean; Lean proves $\alpha(C_5^{\boxtimes 2}) \ge 5$ and $\alpha(C_5^{\boxtimes d})^2 \le 5^d$.
   - Correction: "a zero-Mathlib, six-kernel-checked proof of Haemers's 1979 Schläfli-graph example"; drop "first"; state the integer inequalities and say that $\Theta(C_5) = \sqrt{5}$ follows outside Lean.
   - Affects a theorem statement: no.

8. **Theorem T1c (`main.tex`:195–200).**
   - What is wrong: part (i) assumes $n \ge 5$ and $|\delta_y| = 1$ or $|\delta_z| = 1$; Lean (`Challenge.lean`:40–63) assumes $n \ge 9$ and proves only the branch $e_3 - 2e_0 = \pm 1$. Part (ii) states $|B_Q(H^*)| = 45 < 49$ "for all $n \ge 15$"; Lean evaluates the ball sizes at $n = 19, 21, 23, 25$ only, with stand-alone counting functions not tied to the subgroups.
   - Correction: "for $n \ge 9$, every shift with $e_3 - 2e_0 = \pm 1$ conflicts with another point of its own $H_{\mathrm{BPZ}}$ coset; for $n \ge 15$ the $H^*$ shift $(0,0,\pm 1,0)$ is private; ball sizes 45 versus 49 evaluated at $n = 19, 21, 23, 25$".
   - Affects a theorem statement: yes.

9. **Theorem T4b, hypothesis (iii) (`main.tex`:392).**
   - What is wrong: the paper states $\|w_v\|^2 \le D$; Lean (`Challenge.lean`:164) requires $\|w_v\|^2 = D$ for all $v$.
   - Correction: $\|w_v\|^2 = D$.
   - Affects a theorem statement: yes.

10. **Theorems T1d and T1e: missing prior-work credit (`main.tex`, Pillar I; `references.bib`).**
    - What is wrong: CGR 2003 is not cited. All T1e cardinalities are published: for odd $k$, $M_k n^2 = n^2(n^2-n-8)/16$ is CGR Theorem 1 at $d = 3$ (checked for $k = 3, 5, 7, 9$ and against Table 1 at $n = 25, 41, 57$); for even $k$ it is $(n^4-n^3)/16$, the Baumert et al. (1971) value quoted on CGR p. 246. For T1d, $m \equiv 0 \pmod 4$ gives the same Baumert et al. value, and $n = 21$ (11466 words) is in the Buys–Polak–Zuiddam repository (`ShannonBounds/CosetC21.lean`).
    - Correction: cite CGR 2003; next to T1d and T1e say which cardinalities were published and what is new (coset description, port pattern, T1d sizes for $n \equiv 5 \pmod{16}$, $n \ge 37$).
    - Affects a theorem statement: no.

11. **Theorems T1e and T1f: contract statements (`main.tex`, Pillar I).**
    - What is wrong: the prose T1e includes an $n^2$-port `RichPortSystem` for odd $k$, and the prose T1f includes an exact factored cardinality. Neither is in the contract statements `T1eStmt` (`Challenge.lean`:73–91) and `T1fStmt` (:93–102). They are proved in separate declarations (`hstarOddRichPortSystem`, `hstarOddRichPortSystem_sz`, `baumertExpandList_len`, `baumertExpandList_nodup_and_indep`) on the three standard axioms, outside `comparator.json` and `VerifyAxioms.lean`.
    - Correction: say so in the theorem text, or extend the contract.
    - Affects a theorem statement: yes (the prose theorems are larger than the contract statements).

12. **"Newly discovered $H^*$" (abstract, `main.tex`:61; Figure 2 caption, :211).**
    - What is wrong: novelty of the subgroup rests on a string search of a few texts; the code sizes it yields are published values. The same abstract sentence says "unconditional intra-coset privacy for all odd $n \ge 15$" (Lean has no parity hypothesis and evaluates ball sizes at four $n$, item 8) and attributes "exact factored cardinality" to the Baumert map (item 11).
    - Correction: "the subgroup $H^* = \langle(1,0,0,2),(0,1,0,4)\rangle$, which we did not find in the literature we read".
    - Affects a theorem statement: no.

13. **BPZ citation (`references.bib`, entry `bpz2026lean`; `main.tex`:82, :87, :250).**
    - What is wrong: the separation calculus and the coset code come from the Buys–Polak–Zuiddam GitHub repository <https://github.com/spectra-research/shannon-capacity-lean>; the bibliography cites only arXiv:2607.29681v1, which does not contain them.
    - Correction: add a bibliography entry for the repository with commit and date, and say that the $C_{25}$/$C_{29}$ coset codes and the $C_{27}$/$C_{31}$ expansion-plus-ports steps follow the BPZ $C_{21} \to C_{23}$ construction.
    - Affects a theorem statement: no.

14. **Citation-check count (documentation, not the paper: `docs/run-log.md`, `docs/10-pass-review.md`, `docs/threat-model.md`, `docs/reviews/adversarial-red-team-review.md`; now corrected).**
    - What is wrong: "20/20 bibliography entries parsed and resolved" cannot be true: `scripts/check_citations.py` builds a URL only from a DOI, arXiv id or URL, and `baumert1971combinatorial` has none, so at most 19 entries can be checked.
    - Correction: report checked and skipped entries separately.
    - Affects a theorem statement: no.

15. **Work title (`CITATION.cff`:2, `lean/formalization.yaml`:6, paper title).**
    - What is wrong: three different titles were used for this work.
    - Correction: `CITATION.cff` and `lean/formalization.yaml` now use the paper title.
    - Affects a theorem statement: no.

### Other files corrected in a follow-up pass (2026-11-26)

The first pass left these files unchanged. They were corrected on 2026-11-26 in a second pass:

- `THIRD_PARTY_NOTICES.md`: the titles of arXiv:2607.27869 (*A Recursive Construction Improving the Lower Bound on the Shannon Capacity of $C_7$*) and arXiv:2608.30273 (*Strengthening Recursive Constructions for Zero-Error Shannon Capacity*) are corrected, the claim that T3c resolves "Open Problem #2" is removed, and CGR 2003 is credited.
- `AGENTS.md` and the generated `llms-full.txt`: the "records" wording and the third-power comparison are removed, and the four printed values are now the Lean values $12.344196091426841$, $13.319390984674515$, $14.319949949077991$, $15.308776193986504$ (they had printed $\ldots840$, $\ldots516$, $\ldots992$, $\ldots503$; two of those are larger than what is proved).
- `docs/site/index.html` (project site) and `docs/media/social-preview.svg` (README image): "world records", the third-power gains, "first" and "paradox" are removed; the comparison is with CGR 2003 Table 1, and the Lovász values are corrected as in item 3(d).
- `CHANGELOG.md`: a dated correction note is added to the `1.0.0` entry; the entry itself is kept.

Still not corrected (outside the files edited in these passes): the `description` in `repo.yaml` ("world records"); the third-power baselines and gains in `data/witnesses.json`; the "Paradox" label for T4d in `docs/site/blueprint-data.json`, which `scripts/build_blueprint.py` regenerates; and `scripts/generate_figures.py`, which would rewrite `docs/media/social-preview.svg` with the old text.

### Known issues in the formal code (not yet fixed)

None of these affects the correctness of a proved statement.

- `lean/ZeroErrorFrontier/WorldRecords.lean`: the theorem names `t2b_c27_world_record` and `t2d_c31_world_record` and their docstrings call the $C_{27}$ and $C_{31}$ bounds world records. They are below the 2003 published values (item 1). Renaming would change the comparator contract, so the names are kept in `v1.0.0`.
- `lean/ZeroErrorFrontier/SeparationCalculus.lean`:21–22, :501 and :596–597: the module docstring, a section header and the T3c docstring say T3c resolves Tandon's "Open Problem #2" (item 5). The statement itself (`lean/Challenge.lean`:144–152) is correct as a two-alphabet combining rule.
- `lean/Challenge.lean`:40–63 (`T1cStmt`): states only the branch $e_3 - 2e_0 = \pm 1$, with $9 \le n$, and ball sizes at four fixed $n$; the docstring mentions a second branch ("and similarly e2 - 2*e1") that the statement omits (item 8).
- `lean/ZeroErrorFrontier/AdversarialTests.lean`:36: `boundary_hbpz_fails_at_n7` tests `liftHStar` at $n = 7$, not $H_{\mathrm{BPZ}}$. No test covers $n = 8$ ($H_{\mathrm{BPZ}}$) or $n = 14$ ($H^*$), so the thresholds 9 and 15 are not shown to be sharp.
- `lean/ZeroErrorFrontier/AdversarialTests.lean`: the name `schlafli_sharp_ceilings` overstates; the bound $7^d$ for the complement is not sharp for $\alpha(\overline{G_{27}}) = 6$.
- `lean/ZeroErrorFrontier/NonVacuity.lean`:153: `nonvacuity_t3c` exercises the one-alphabet lift `liftT3c`; `heteroCompose` is never instantiated with two different alphabets.
- `lean/VerifyAxioms.lean` and `lean/comparator.json` do not include `hstarOddRichPortSystem`, `hstarOddRichPortSystem_sz`, `baumertExpandList_len` and `baumertExpandList_nodup_and_indep`, although the prose cites them (item 11).
- `lean/ZeroErrorFrontier/CosetQuotient.lean`: the name `t1b_exact_quotient_ceilings` says "exact", but the statement is an upper bound only; attainment is shown only for the $n$ covered by T1d, T1e and T2c.
