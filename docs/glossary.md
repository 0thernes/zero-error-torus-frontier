# Glossary (`zero-error-torus-frontier`)

- **Strong graph product ($G \boxtimes H$):** Graph on $V(G) \times V(H)$ where distinct $(u_1,v_1) \neq (u_2,v_2)$ are adjacent iff $(u_1=u_2 \lor u_1 \sim_G u_2)$ and $(v_1=v_2 \lor v_1 \sim_H v_2)$.
- **Shannon capacity ($\Theta(G)$):** $\sup_{d \ge 1} \alpha(G^{\boxtimes d})^{1/d}$, the maximum zero-error asymptotic transmission rate per channel use (Shannon, 1956).
- **Lovász theta ($\vartheta(G)$):** Semidefinite programming upper bound satisfying $\Theta(G) \le \vartheta(G)$; for odd cycles $\vartheta(C_n) = n\cos(\pi/n)/(1+\cos(\pi/n))$.
- **Haemers bound:** Linear-algebraic upper bound $\Theta(G) \le \min \mathrm{rank}_F(M)$ over matrices $M$ fitting $G$ ($M_{vv} \neq 0$, $M_{uv}=0$ on non-edges).
- **Coset-quotient compression:** Quotienting $C_n^{\boxtimes 4}$ by a 2D subgroup $H \le \mathbb{Z}_n^4$ of size $n^2$ so independent sets $Q$ in a 2D quotient graph lift $n^2$-to-1 to $I = Q + H$.
- **$H_{\mathrm{BPZ}}$ vs. $H^*$:** $H_{\mathrm{BPZ}} = \langle(1,0,0,2),(0,1,2,0)\rangle$ has forbidden ball size $49$ ($7\times 7$) and unit-shift intra-coset port obstruction; our $H^* = \langle(1,0,0,2),(0,1,0,4)\rangle$ has forbidden ball size $45$ ($3\times 15$) and unconditional intra-coset privacy for $n \ge 15$.
- **RichPortSystem:** Structured 7-block independent configuration $(B,N,A,D,O,H,V)$ realizing the 7-letter separation predicate `Letter.sep` for recursive strong-power capacity lifts.
- **Baumert pullback ($\varphi : \mathbb{Z}_{p+2} \to \mathbb{Z}_p$):** Locally-injective graph homomorphism $\varphi(x) = x$ ($x<2$), $x-2$ ($x \ge 2$) lifting independent sets from $C_p^{\boxtimes d}$ to $C_{p+2}^{\boxtimes d}$.
- **81-ball certificate:** Pure-kernel verification method certifying port/footprint privacy by inspecting only the $3^4 = 81$ unit-cube neighbors around each port using $O(1)$ bitmask quotient membership.
- **Palomar Comparator:** Lean 4.35.0 built-in verification harness (`lake comparator --config comparator.json --paranoid`) that replays targets across 6 independent proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).
- **Schläfli graph ($G_{27}$):** Strongly regular $(27,16,10,8)$ graph whose complement $\overline{G_{27}}$ encodes the 27 lines on a smooth cubic surface; used by Haemers (1979) to refute $\Theta(G \boxtimes H) = \Theta(G)\Theta(H)$.
