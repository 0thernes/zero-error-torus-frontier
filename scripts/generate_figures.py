# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Generate all 5 publication-grade vector PDF/PNG figures and social preview assets."""

from __future__ import annotations

import json
import math
import pathlib
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.patches as mpatches
import matplotlib.pyplot as plt
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
sys.path.insert(0, str(ROOT / "reference"))

from capacity_oracle import _load_lean_tables, apply_table, eval_code
from torus_frontier.verifier import Q25_HBPZ, SEP_G7, hstar_family, schlafli_comp_adj

FIG_DIR = ROOT / "paper" / "figures"
MEDIA_DIR = ROOT / "docs" / "media"
FIG_DIR.mkdir(parents=True, exist_ok=True)
MEDIA_DIR.mkdir(parents=True, exist_ok=True)

# Colorblind-safe Okabe-Ito publication palette
PAL = {
    "navy": "#1B365D",
    "blue": "#0072B2",
    "sky": "#56B4E9",
    "teal": "#009E73",
    "orange": "#E69F00",
    "vermilion": "#D55E00",
    "purple": "#CC79A7",
    "slate": "#4A5568",
    "light": "#F7FAFC",
    "grid": "#CBD5E0",
}

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.2,
    "axes.labelsize": 9.3,
    "xtick.labelsize": 8.4,
    "ytick.labelsize": 8.4,
    "legend.fontsize": 7.8,
    "axes.edgecolor": "#334155",
    "axes.linewidth": 0.8,
    "pdf.fonttype": 42,
    "ps.fonttype": 42,
})


def lovasz_theta(n: int) -> float:
    c = math.cos(math.pi / n)
    return n * c / (1.0 + c)


def fig1_odd_cycle_frontier() -> None:
    """Fig 1: Shannon capacity frontier for odd cycles C_25..C_31 vs Baumert-Hales and Lovasz theta."""
    ns = [25, 27, 29, 31]
    bh = [12.3310604178, 13.3176204000, 14.3045513000, 15.2906289000]
    d4_base = [23125 ** 0.25, 31466 ** 0.25, 42050 ** 0.25, 54913 ** 0.25]
    ours = [12.344196091426841, 13.319390984674515, 14.319949949077991, 15.308776193986504]
    lov = [lovasz_theta(n) for n in ns]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.8, 4.1), dpi=300)

    x = np.arange(len(ns))
    w = 0.26
    gap_bh = [lov[i] - bh[i] for i in range(4)]
    gap_base = [lov[i] - d4_base[i] for i in range(4)]
    gap_ours = [lov[i] - ours[i] for i in range(4)]

    ax1.bar(x - w, gap_bh, width=w, color=PAL["slate"], alpha=0.75, label="Baumert–Hales (1971–73, $d=3$)")
    ax1.bar(x, gap_base, width=w, color=PAL["sky"], edgecolor=PAL["blue"], lw=0.7, label=r"Our $d=4$ base ($H^*$/$H_{\mathrm{BPZ}}$/Baumert)")
    ax1.bar(x + w, gap_ours, width=w, color=PAL["vermilion"], edgecolor="#7F1D1D", lw=0.7, label="Our certified record (Lean 4.35)")
    for i in range(4):
        ax1.text(x[i] - w, gap_bh[i] + 0.003, f"{gap_bh[i]:.4f}", ha="center", va="bottom", fontsize=6.8, color=PAL["slate"])
        ax1.text(x[i] + w + 0.05, gap_ours[i] + 0.003, f"{gap_ours[i]:.4f}", ha="center", va="bottom", fontsize=7.0, color="#7F1D1D", fontweight="bold")

    ax1.set_xticks(x)
    ax1.set_xticklabels([f"$C_{{{n}}}$" for n in ns])
    ax1.set_ylabel(r"Gap to Lovász upper bound $\vartheta(C_n) - \mathrm{LB}$")
    ax1.set_title(r"(a) Residual gap to $\vartheta(C_n)$ (lower is tighter)")
    ax1.set_ylim(0, 0.235)
    ax1.grid(axis="y", ls="--", alpha=0.45, color=PAL["grid"])
    ax1.legend(loc="upper left", frameon=True, facecolor="white", framealpha=0.95)

    gains = [ours[i] - bh[i] for i in range(4)]
    port_gains = [ours[i] - d4_base[i] for i in range(4)]
    base_gains = [d4_base[i] - bh[i] for i in range(4)]
    ax2.bar(x, base_gains, width=0.50, color=PAL["blue"], label="$d=4$ algebraic gain over B–H")
    ax2.bar(x, port_gains, bottom=base_gains, width=0.50, color=PAL["orange"], edgecolor="#92400E", lw=0.7, label="Port-calculus lift ($p=144$ / $2048$)")
    for i in range(4):
        ax2.text(x[i], gains[i] + 0.0005, f"+{gains[i]:.6f}", ha="center", va="bottom", fontsize=7.5, fontweight="bold", color=PAL["navy"])
    ax2.axhline(0, color="#1E293B", lw=0.8)
    ax2.set_xticks(x)
    ax2.set_xticklabels([f"$C_{{{n}}}$\n($p={p}$)" for n, p in zip(ns, [144, 2048, 4, 2048])])
    ax2.set_ylabel("Capacity gain over Baumert–Hales")
    ax2.set_title("(b) Net gain over 1971–73 $d=3$ bounds")
    ax2.set_ylim(0, 0.0265)
    ax2.grid(axis="y", ls="--", alpha=0.45, color=PAL["grid"])
    ax2.legend(loc="upper left", frameon=True, facecolor="white", framealpha=0.95)

    fig.tight_layout(pad=1.2)
    fig.savefig(FIG_DIR / "fig1_odd_cycle_frontier.pdf")
    fig.savefig(FIG_DIR / "fig1_odd_cycle_frontier.png", dpi=220)
    plt.close(fig)


def fig2_hbpz_vs_hstar_torus() -> None:
    """Fig 2: Side-by-side 2D quotient torus comparison: H_BPZ (49-ball, 37 cosets) vs H* (45-ball, 37 cosets + ports)."""
    n = 25
    _, q25_hstar = hstar_family(3)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 5.0), dpi=300)

    ax1.set_facecolor("#F8FAFC")
    ox, oy = Q25_HBPZ[0]
    for dy in range(-3, 4):
        for dz in range(-3, 4):
            ry = (ox + dy) % n
            rz = (oy + dz) % n
            ax1.add_patch(mpatches.Rectangle((ry - 0.5, rz - 0.5), 1, 1, facecolor=PAL["sky"], alpha=0.28, edgecolor="none"))
    ax1.scatter([p[0] for p in Q25_HBPZ], [p[1] for p in Q25_HBPZ], s=36, color=PAL["navy"], zorder=4, label=r"$Q_{25}$ ($|Q|=37$, $49$-ball)")
    ax1.scatter([ox], [oy], s=68, color=PAL["vermilion"], marker="s", zorder=5, label=r"Origin $(0,14)$ & $7{\times}7$ ball")
    ax1.set_xlim(-0.8, 24.8)
    ax1.set_ylim(-0.8, 24.8)
    ax1.set_aspect("equal")
    ax1.set_xlabel(r"Quotient coordinate $y \in \mathbb{Z}_{25}$")
    ax1.set_ylabel(r"Quotient coordinate $z \in \mathbb{Z}_{25}$")
    ax1.set_title(r"(a) $H_{\mathrm{BPZ}} = \langle(1,0,0,2),(0,1,2,0)\rangle$ ($|B_Q|=49$)")
    ax1.grid(True, ls=":", alpha=0.45, color=PAL["grid"])
    ax1.legend(loc="upper center", bbox_to_anchor=(0.5, -0.15), ncol=1, fontsize=7.6, frameon=True, facecolor="white")

    ax2.set_facecolor("#F8FAFC")
    for dy in range(-1, 2):
        for dz in range(-7, 8):
            ry = dy % n
            rz = dz % n
            ax2.add_patch(mpatches.Rectangle((ry - 0.5, rz - 0.5), 1, 1, facecolor=PAL["teal"], alpha=0.22, edgecolor="none"))
    xq = [((y + 1) % n, (z - 1) % n) for y, z in q25_hstar]
    ax2.scatter([p[0] for p in xq], [p[1] for p in xq], s=22, color=PAL["orange"], alpha=0.72, marker="^", zorder=3, label=r"Shifted $X_q = Q^* + (1,-1)$")
    ax2.scatter([p[0] for p in q25_hstar], [p[1] for p in q25_hstar], s=36, color=PAL["teal"], edgecolor="#064E3B", lw=0.5, zorder=4, label=r"$Q^*_{25}$ ($|Q^*|=37$, $45$-ball)")
    ax2.scatter([0], [0], s=84, color=PAL["blue"], marker="o", edgecolor="white", lw=0.9, zorder=6, label=r"Owner $p_0=(0,0)$")
    ax2.scatter([24], [0], s=92, color=PAL["vermilion"], marker="*", zorder=6, label=r"Private handle $p_1=(24,0)$")
    ax2.set_xlim(-0.8, 24.8)
    ax2.set_ylim(-0.8, 24.8)
    ax2.set_aspect("equal")
    ax2.set_xlabel(r"Quotient coordinate $y \in \mathbb{Z}_{25}$")
    ax2.set_ylabel(r"Quotient coordinate $z \in \mathbb{Z}_{25}$")
    ax2.set_title(r"(b) New $H^* = \langle(1,0,0,2),(0,1,0,4)\rangle$ ($|B_Q|=45$, $625$ ports)")
    ax2.grid(True, ls=":", alpha=0.45, color=PAL["grid"])
    ax2.legend(loc="upper center", bbox_to_anchor=(0.5, -0.15), ncol=2, fontsize=7.4, frameon=True, facecolor="white")

    fig.tight_layout(pad=1.2)
    fig.subplots_adjust(bottom=0.20, top=0.91)
    fig.savefig(FIG_DIR / "fig2_hbpz_vs_hstar_torus.pdf", bbox_inches="tight", pad_inches=0.08)
    fig.savefig(FIG_DIR / "fig2_hbpz_vs_hstar_torus.png", dpi=220, bbox_inches="tight", pad_inches=0.08)
    plt.close(fig)


def fig3_g7_c5_and_barriers() -> None:
    """Fig 3: 7-letter separation graph G_7 highlighting the induced C_5 engine and fractional barrier."""
    tbls = _load_lean_tables()
    w0 = {"B": 22500, "N": 21875, "A": 625, "D": 625, "O": 625, "H": 625, "V": 625}
    w1 = apply_table(tbls["T3c"], w0)
    w2 = apply_table(tbls["T3e"], w1)
    val_base = 23125 ** 0.25
    val_c4b_direct = math.exp(math.log(eval_code(tbls["C4b"], w0)) / 16.0)
    val_t3c_c4b = math.exp(math.log(eval_code(tbls["C4b"], w1)) / 48.0)
    val_full = math.exp(math.log(eval_code(tbls["C4b"], w2)) / 144.0)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.8, 4.3), dpi=300, gridspec_kw={"width_ratios": [1.0, 1.35]})

    pos = {
        "B": (0.0, 1.00),
        "A": (0.95, 0.30),
        "V": (0.58, -0.78),
        "H": (-0.58, -0.78),
        "D": (-0.95, 0.30),
        "O": (0.0, -0.06),
        "N": (0.0, 1.66),
    }
    letters = ["B", "N", "A", "D", "O", "H", "V"]
    c5_edges = {frozenset(e) for e in [("B", "A"), ("A", "V"), ("V", "H"), ("H", "D"), ("D", "B")]}

    for i in range(7):
        for j in range(i + 1, 7):
            if not SEP_G7[i][j]:
                u, v = letters[i], letters[j]
                is_c5 = frozenset((u, v)) in c5_edges
                ax1.plot(
                    [pos[u][0], pos[v][0]],
                    [pos[u][1], pos[v][1]],
                    color=PAL["vermilion"] if is_c5 else PAL["slate"],
                    lw=2.6 if is_c5 else 1.0,
                    ls="-" if is_c5 else "--",
                    alpha=0.95 if is_c5 else 0.50,
                    zorder=2 if is_c5 else 1,
                )

    node_colors = {
        "B": PAL["vermilion"],
        "A": PAL["vermilion"],
        "V": PAL["vermilion"],
        "H": PAL["vermilion"],
        "D": PAL["vermilion"],
        "O": PAL["blue"],
        "N": PAL["teal"],
    }
    for letter, (px, py) in pos.items():
        ax1.scatter([px], [py], s=370, color=node_colors[letter], edgecolor="white", lw=1.6, zorder=4)
        ax1.text(px, py, letter, ha="center", va="center", color="white", fontweight="bold", fontsize=9.5, zorder=5)

    ax1.set_xlim(-1.45, 1.45)
    ax1.set_ylim(-1.15, 2.02)
    ax1.set_aspect("equal")
    ax1.axis("off")
    ax1.set_title("(a) $G_7$ & induced $C_5$ (B–A–V–H–D)")
    p_c5 = mpatches.Patch(color=PAL["vermilion"], label="Induced chordless $C_5$ core")
    p_o = mpatches.Patch(color=PAL["blue"], label="Hub O (adj. {A, D, H, V})")
    p_n = mpatches.Patch(color=PAL["teal"], label="Pendant N (adj. only B)")
    ax1.legend(handles=[p_c5, p_o, p_n], loc="upper center", bbox_to_anchor=(0.5, -0.02), fontsize=7.4, frameon=True, facecolor="white")

    stages = [
        "Base $d=4$\n($p=4$)",
        "C4b direct\n($p=16$)",
        r"T3c$\to$C4b" + "\n($p=48$)",
        r"T3c$\to$T3e$\to$C4b" + "\n($p=144$)",
        "T3b Barrier\n$(46875/2)^{1/4}$",
        "Lovász\n$\\vartheta(C_{25})$",
    ]
    vals = [val_base, val_c4b_direct, val_t3c_c4b, val_full, (46875.0 / 2.0) ** 0.25, lovasz_theta(25)]
    cols = [PAL["sky"], "#38A3D1", PAL["blue"], PAL["vermilion"], PAL["orange"], PAL["slate"]]
    y_pos = np.arange(len(stages))
    x0 = 12.32
    ax2.barh(y_pos, [v - x0 for v in vals], left=x0, height=0.58, color=cols, edgecolor="#1E293B", lw=0.6)
    for i, v in enumerate(vals):
        ax2.text(v + 0.0022, y_pos[i], f"{v:.6f}", va="center", ha="left", fontsize=7.5, fontweight="bold" if i in (3, 4) else "normal")
    ax2.set_yticks(y_pos)
    ax2.set_yticklabels(stages, fontsize=7.8)
    ax2.set_xlim(x0, 12.495)
    ax2.set_xlabel(r"Effective capacity bound for $C_{25}$")
    ax2.set_title(r"(b) $C_{25}$ lift progression vs. T3b barrier & $\vartheta(C_{25})$")
    ax2.grid(axis="x", ls="--", alpha=0.45, color=PAL["grid"])

    fig.tight_layout(pad=1.2)
    fig.subplots_adjust(bottom=0.20)
    fig.savefig(FIG_DIR / "fig3_g7_c5_and_barriers.pdf")
    fig.savefig(FIG_DIR / "fig3_g7_c5_and_barriers.png", dpi=220)
    plt.close(fig)


def fig4_baumert_pullback_ports() -> None:
    """Fig 4: Baumert pullback port geometry for C_27 (88 ports) and C_31 (133 ports) + T2a^k lift curve."""
    wdata = json.loads((ROOT / "data" / "witnesses.json").read_text(encoding="utf-8"))
    c27 = wdata["c27_baumert_ports"]
    c31 = wdata["c31_baumert_ports"]
    tbls = _load_lean_tables()

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 3.9), dpi=300)

    cats = ["$C_{25}$ ($H^*$)\n$N=23{,}125$", "$C_{27}$ (Baumert)\n$N=31{,}466$", "$C_{31}$ (Baumert)\n$N=54{,}913$"]
    d_vals = [625, len(c27["ports"]), len(c31["ports"])]
    a_vals = [625, len(c27["A"]), len(c31["A"])]
    dd_vals = [625, len(c27["D"]), len(c31["D"])]
    x = np.arange(3)
    w = 0.24
    ax1.bar(x - w, d_vals, width=w, color=PAL["blue"], label="Private ports $d = |O| = |H|$")
    ax1.bar(x, a_vals, width=w, color=PAL["orange"], label="Owner footprint $|A|$")
    ax1.bar(x + w, dd_vals, width=w, color=PAL["teal"], label="Handle footprint $|D|$")
    for i in range(3):
        ax1.text(x[i] - w, d_vals[i] + 14, str(d_vals[i]), ha="center", va="bottom", fontsize=7.6, fontweight="bold")
        ax1.text(x[i], a_vals[i] + 14, str(a_vals[i]), ha="center", va="bottom", fontsize=7.6)
        ax1.text(x[i] + w, dd_vals[i] + 14, str(dd_vals[i]), ha="center", va="bottom", fontsize=7.6)
    ax1.set_xticks(x)
    ax1.set_xticklabels(cats)
    ax1.set_ylabel(r"Cardinality in $C_n^{\boxtimes 4}$")
    ax1.set_title("(a) Certified port & footprint profiles")
    ax1.set_ylim(0, 745)
    ax1.grid(axis="y", ls="--", alpha=0.45, color=PAL["grid"])
    ax1.legend(loc="upper right", fontsize=7.6, frameon=True, facecolor="white")

    ks = list(range(8))

    def curve(w0: dict[str, int], base_n: int) -> list[float]:
        base_val = base_n ** 0.25
        w_cur = dict(w0)
        res = []
        for k in ks:
            if k > 0:
                w_cur = apply_table(tbls["T2a"], w_cur)
            m = eval_code(tbls["C4a"], w_cur)
            p = 4 * (2 ** k) * 4
            val = math.exp(math.log(m) / p)
            res.append((val - base_val) * 1e4)
        return res

    g27 = curve({"B": 31378, "N": 31079, "A": 237, "D": 150, "O": 88, "H": 88, "V": 88}, 31466)
    g31 = curve({"B": 54780, "N": 54371, "A": 337, "D": 205, "O": 133, "H": 133, "V": 133}, 54913)

    ax2.plot(ks, g27, marker="o", color=PAL["blue"], lw=2.0, label=r"$C_{27}$ ($d=88$, $p=16 \cdot 2^k$)")
    ax2.plot(ks, g31, marker="s", color=PAL["vermilion"], lw=2.0, label=r"$C_{31}$ ($d=133$, $p=16 \cdot 2^k$)")
    ax2.scatter([7], [g27[7]], s=80, color=PAL["blue"], edgecolor="black", zorder=5)
    ax2.scatter([7], [g31[7]], s=80, color=PAL["vermilion"], edgecolor="black", zorder=5)
    ax2.annotate(
        f"$C_{{31}}$ ($p=2048$)\n+{g31[7]:.2f}$\\times 10^{{-4}}$",
        xy=(7, g31[7]),
        xytext=(3.2, 7.6),
        arrowprops={"arrowstyle": "->", "color": PAL["vermilion"], "lw": 1.2},
        fontsize=7.6,
        color=PAL["vermilion"],
        fontweight="bold",
    )
    ax2.annotate(
        f"$C_{{27}}$ ($p=2048$)\n+{g27[7]:.2f}$\\times 10^{{-4}}$",
        xy=(7, g27[7]),
        xytext=(2.6, 5.2),
        arrowprops={"arrowstyle": "->", "color": PAL["blue"], "lw": 1.2},
        fontsize=7.6,
        color=PAL["blue"],
        fontweight="bold",
    )
    ax2.set_xticks(ks)
    ax2.set_xticklabels([f"$k={k}$\n({16*(2**k)})" for k in ks], fontsize=7.3)
    ax2.set_ylabel(r"Lift over $d=4$ base ($\times 10^{-4}$)")
    ax2.set_ylim(0, 9.2)
    ax2.set_title(r"(b) Iterated $\mathrm{T2a}^k \to \mathrm{C4a}$ capacity convergence")
    ax2.grid(True, ls="--", alpha=0.45, color=PAL["grid"])
    ax2.legend(loc="lower right", fontsize=7.6, frameon=True, facecolor="white")

    fig.tight_layout(pad=1.2)
    fig.savefig(FIG_DIR / "fig4_baumert_pullback_ports.pdf")
    fig.savefig(FIG_DIR / "fig4_baumert_pullback_ports.png", dpi=220)
    plt.close(fig)


def fig5_schlafli_paradox_spectra() -> None:
    """Fig 5: Haemers's 1979 Schlafli Paradox — adjacency structure of G_27^c & capacity super-multiplicativity."""
    adj_comp = np.zeros((27, 27), dtype=int)
    for u in range(27):
        for v in range(27):
            if schlafli_comp_adj(u, v):
                adj_comp[u, v] = 1

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 4.0), dpi=300)

    mat = adj_comp + np.eye(27, dtype=int)
    ax1.imshow(mat, cmap="Blues", interpolation="nearest", aspect="equal")
    for b in (5.5, 11.5):
        ax1.axhline(b, color=PAL["vermilion"], lw=1.2, ls="--")
        ax1.axvline(b, color=PAL["vermilion"], lw=1.2, ls="--")
    ax1.set_xticks([2.5, 8.5, 19.0])
    ax1.set_xticklabels(["$a_0..a_5$", "$b_0..b_5$", "$c_{ij}$ (15)"])
    ax1.set_yticks([2.5, 8.5, 19.0])
    ax1.set_yticklabels(["$a_0..a_5$", "$b_0..b_5$", "$c_{ij}$ (15)"])
    ax1.set_title(r"(a) $I + A(G_{27}^c)$: exact $\mathbb{F}_2$-rank $= 7$ (T4a)")

    bars = [
        r"$\Theta(G_{27}) \leq 3$" + "\n" + r"($\mathbb{Z}^8$ handle, T4b)",
        r"$\Theta(G_{27}^c) \leq 7$" + "\n" + r"($\mathbb{F}_2$ rank-7, T4a)",
        r"$\Theta(G_{27})\cdot\Theta(G_{27}^c)$" + "\n" + r"$\leq 21$",
        r"$\Theta(G_{27}\boxtimes G_{27}^c)$" + "\n" + r"$\geq 27$ (diag.)",
    ]
    heights = [3, 7, 21, 27]
    colors = [PAL["teal"], PAL["blue"], PAL["orange"], PAL["vermilion"]]
    x = np.arange(4)
    ax2.bar(x, heights, width=0.54, color=colors, edgecolor="#1E293B", lw=0.7)
    for i, h in enumerate(heights):
        ax2.text(x[i], h + 0.65, str(h), ha="center", va="bottom", fontsize=9.5, fontweight="bold")
    ax2.annotate(
        "Haemers gap\n$27 > 21$",
        xy=(2.74, 25.5),
        xytext=(1.15, 24.5),
        arrowprops={"arrowstyle": "->", "color": PAL["vermilion"], "lw": 1.4},
        fontsize=8.6,
        fontweight="bold",
        color=PAL["vermilion"],
        bbox={"boxstyle": "round,pad=0.3", "facecolor": "#FFF5F5", "edgecolor": PAL["vermilion"]},
    )
    ax2.set_xticks(x)
    ax2.set_xticklabels(bars, fontsize=7.5)
    ax2.set_ylim(0, 31.5)
    ax2.set_ylabel("Shannon capacity bound")
    ax2.set_title("(b) Super-multiplicativity paradox (T4d, 6-kernel Lean)")
    ax2.grid(axis="y", ls="--", alpha=0.45, color=PAL["grid"])

    fig.tight_layout(pad=1.2)
    fig.savefig(FIG_DIR / "fig5_schlafli_paradox_spectra.pdf")
    fig.savefig(FIG_DIR / "fig5_schlafli_paradox_spectra.png", dpi=220)
    plt.close(fig)


def generate_social_preview() -> None:
    """Generate crisp 1280x640 GitHub social preview SVG (Build Standard A26)."""
    svg = """<svg xmlns="http://www.w3.org/2000/svg" width="1280" height="640" viewBox="0 0 1280 640">
  <defs>
    <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1">
      <stop offset="0%" stop-color="#0B132B"/>
      <stop offset="55%" stop-color="#1C2541"/>
      <stop offset="100%" stop-color="#1B365D"/>
    </linearGradient>
    <linearGradient id="acc" x1="0" y1="0" x2="1" y2="0">
      <stop offset="0%" stop-color="#00B4D8"/>
      <stop offset="100%" stop-color="#F77F00"/>
    </linearGradient>
  </defs>
  <rect width="1280" height="640" fill="url(#bg)"/>
  <rect x="0" y="0" width="1280" height="8" fill="url(#acc)"/>
  <text x="72" y="108" fill="#56B4E9" font-family="Segoe UI, Arial, sans-serif" font-size="22" font-weight="700" letter-spacing="2">0TH-2026-016 · ZERO-MATHLIB LEAN 4.35.0 · 6 PROOF KERNELS</text>
  <text x="72" y="182" fill="#FFFFFF" font-family="Georgia, serif" font-size="54" font-weight="700">Zero-Error Torus Frontier</text>
  <text x="72" y="232" fill="#CBD5E1" font-family="Segoe UI, Arial, sans-serif" font-size="25">Coset-Quotient Compression · 4 Odd-Cycle World Records · Haemers Schläfli Paradox</text>
  <rect x="72" y="274" width="268" height="170" rx="12" fill="#111C38" stroke="#00B4D8" stroke-width="2"/>
  <text x="96" y="316" fill="#56B4E9" font-family="Segoe UI, Arial, sans-serif" font-size="20" font-weight="700">Θ(C₂₅) ≥ 12.344196</text>
  <text x="96" y="352" fill="#E2E8F0" font-family="Consolas, monospace" font-size="16">H* 45-ball + 625 ports</text>
  <text x="96" y="384" fill="#10B981" font-family="Consolas, monospace" font-size="17">+0.013136 vs B–H</text>
  <text x="96" y="418" fill="#94A3B8" font-family="Consolas, monospace" font-size="14">p = 144 · Lean + Rust + C11</text>

  <rect x="364" y="274" width="268" height="170" rx="12" fill="#111C38" stroke="#E69F00" stroke-width="2"/>
  <text x="388" y="316" fill="#FBBF24" font-family="Segoe UI, Arial, sans-serif" font-size="20" font-weight="700">Θ(C₂₇) ≥ 13.319391</text>
  <text x="388" y="352" fill="#E2E8F0" font-family="Consolas, monospace" font-size="16">Baumert + 88 ports</text>
  <text x="388" y="384" fill="#10B981" font-family="Consolas, monospace" font-size="17">+0.001771 vs B–H</text>
  <text x="388" y="418" fill="#94A3B8" font-family="Consolas, monospace" font-size="14">p = 2048 · 81-ball cert</text>

  <rect x="656" y="274" width="268" height="170" rx="12" fill="#111C38" stroke="#009E73" stroke-width="2"/>
  <text x="680" y="316" fill="#34D399" font-family="Segoe UI, Arial, sans-serif" font-size="20" font-weight="700">Θ(C₂₉) ≥ 14.319950</text>
  <text x="680" y="352" fill="#E2E8F0" font-family="Consolas, monospace" font-size="16">50-coset exact ceiling</text>
  <text x="680" y="384" fill="#10B981" font-family="Consolas, monospace" font-size="17">+0.015399 vs B–H</text>
  <text x="680" y="418" fill="#94A3B8" font-family="Consolas, monospace" font-size="14">p = 4 · 42,050 words</text>

  <rect x="948" y="274" width="260" height="170" rx="12" fill="#111C38" stroke="#D55E00" stroke-width="2"/>
  <text x="972" y="316" fill="#FB923C" font-family="Segoe UI, Arial, sans-serif" font-size="20" font-weight="700">Θ(C₃₁) ≥ 15.308776</text>
  <text x="972" y="352" fill="#E2E8F0" font-family="Consolas, monospace" font-size="16">Baumert + 133 ports</text>
  <text x="972" y="384" fill="#10B981" font-family="Consolas, monospace" font-size="17">+0.018147 vs B–H</text>
  <text x="972" y="418" fill="#94A3B8" font-family="Consolas, monospace" font-size="14">p = 2048 · 81-ball cert</text>

  <text x="72" y="514" fill="#E2E8F0" font-family="Segoe UI, Arial, sans-serif" font-size="22">18 Palomar Targets · Zero sorry · Zero native_decide · Θ(G₂₇) ≤ 3, Θ(G₂₇ᶜ) ≤ 7, Θ(G₂₇ ⊠ G₂₇ᶜ) ≥ 27</text>
  <text x="72" y="576" fill="#94A3B8" font-family="Segoe UI, Arial, sans-serif" font-size="20">Alexander Stephen Donahue · ORCID 0009-0006-8168-9648 · github.com/0thernes/zero-error-torus-frontier</text>
</svg>
"""
    (MEDIA_DIR / "social-preview.svg").write_text(svg, encoding="utf-8")


if __name__ == "__main__":
    fig1_odd_cycle_frontier()
    fig2_hbpz_vs_hstar_torus()
    fig3_g7_c5_and_barriers()
    fig4_baumert_pullback_ports()
    fig5_schlafli_paradox_spectra()
    generate_social_preview()
    print("Generated all 5 vector PDF/PNG figures and docs/media/social-preview.svg")
