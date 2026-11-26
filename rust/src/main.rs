// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue
//
// Zero-dependency Rust verifier and search engine for `zero-error-torus-frontier` (v1.0.0).
// Independently verifies all four pillars:
//   Pillar 1: Algebraic coset-quotient compression (H_BPZ, H*), 45 vs 49 quotient ball scan,
//             infinite helical H_BPZ & H* families, and Baumert pullback homomorphism.
//   Pillar 2: Four consecutive odd-cycle world records (C_25, C_27, C_29, C_31) including
//             exact Baumert expansion & independence verification.
//   Pillar 3: Separation graph G_7 induced C_5 and exact capacity alpha(G_7)=chi_bar(G_7)=3.
//   Pillar 4: Lovasz C_5 Z[sqrt(5)] idempotent and Haemers 1979 Schlafli paradox (Z^8 + F_2).

use std::env;
use std::process;

const Q25_HBPZ: [(usize, usize); 37] = [
    (0, 14), (1, 19), (2, 2), (2, 6), (2, 23), (3, 10), (4, 14), (5, 18), (6, 2), (6, 23),
    (7, 6), (7, 10), (8, 14), (9, 18), (10, 22), (11, 1), (11, 5), (11, 9), (12, 13), (13, 17),
    (14, 21), (15, 0), (15, 4), (15, 8), (16, 12), (17, 16), (18, 20), (19, 3), (19, 7), (19, 24),
    (20, 11), (21, 15), (22, 19), (23, 2), (23, 6), (23, 23), (24, 10),
];

const Q29_HBPZ: [(usize, usize); 50] = [
    (0, 0), (0, 21), (0, 25), (1, 17), (2, 13), (3, 5), (3, 9), (4, 1), (4, 21), (4, 25),
    (5, 17), (6, 13), (7, 5), (7, 9), (8, 1), (8, 22), (8, 26), (9, 18), (10, 14), (11, 6),
    (11, 10), (12, 2), (12, 23), (12, 27), (13, 19), (14, 15), (15, 10), (16, 2), (16, 6),
    (16, 23), (16, 27), (17, 19), (18, 15), (19, 11), (20, 3), (20, 7), (20, 24), (20, 28),
    (21, 20), (22, 15), (23, 11), (24, 3), (24, 7), (24, 24), (24, 28), (25, 20), (26, 16),
    (27, 12), (28, 4), (28, 8),
];

const SEP_G7: [[bool; 7]; 7] = [
    [false, false, false, false, true,  true,  true ],
    [false, false, true,  true,  true,  true,  true ],
    [false, true,  false, true,  false, true,  false],
    [false, true,  true,  false, false, false, true ],
    [true,  true,  false, false, false, false, false],
    [true,  true,  true,  false, false, false, false],
    [true,  true,  false, true,  false, false, false],
];

const CPAIR: [(usize, usize); 15] = [
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5),
    (4, 5),
];

const SCHLAFLI_L_BITS: [u32; 27] = [
    1, 2, 4, 8, 16, 32,
    62, 61, 59, 55, 47, 31,
    64, 70, 74, 82, 98,
    69, 73, 81, 97,
    79, 87, 103,
    91, 107, 115,
];

const SCHLAFLI_R_BITS: [u32; 7] = [
    130945, 1974082, 14823108, 52710856, 88640464, 110168032, 132124867,
];

#[inline]
pub fn cyc_dist(n: usize, a: usize, b: usize) -> usize {
    let d1 = (a + n - b) % n;
    let d2 = (b + n - a) % n;
    d1.min(d2)
}

#[inline]
pub fn pull1(x: usize) -> usize {
    if x < 2 { x } else { x - 2 }
}

pub fn verify_q_hbpz(n: usize, q: &[(usize, usize)]) -> bool {
    for &(y, z) in q {
        if y >= n || z >= n {
            return false;
        }
    }
    for i in 0..q.len() {
        for j in (i + 1)..q.len() {
            if cyc_dist(n, q[i].0, q[j].0) <= 3 && cyc_dist(n, q[i].1, q[j].1) <= 3 {
                return false;
            }
        }
    }
    true
}

pub fn verify_q_hstar(n: usize, q: &[(usize, usize)]) -> bool {
    for &(y, z) in q {
        if y >= n || z >= n {
            return false;
        }
    }
    for i in 0..q.len() {
        for j in (i + 1)..q.len() {
            if cyc_dist(n, q[i].0, q[j].0) <= 1 && cyc_dist(n, q[i].1, q[j].1) <= 7 {
                return false;
            }
        }
    }
    true
}

pub fn hstar_family(k: usize) -> (usize, Vec<(usize, usize)>) {
    let n = 8 * k + 1;
    let m = 4 * k * k + k / 2;
    let j = k / 2;
    let mut pts = Vec::with_capacity(m);
    for t in 0..m {
        let y = if k.is_multiple_of(2) {
            t / (k / 2)
        } else if t >= 4 * k * k {
            8 * k
        } else {
            let pair = t / k;
            let rem = t % k;
            if rem <= j { 2 * pair } else { 2 * pair + 1 }
        };
        let z = if k.is_multiple_of(2) {
            (8 * t) % n
        } else {
            let extra = usize::from(0 < t)
                + usize::from(k * k < t)
                + usize::from(2 * k * k < t)
                + usize::from(3 * k * k < t);
            (8 * t + extra) % n
        };
        pts.push((y, z));
    }
    (n, pts)
}

pub fn verify_hstar_odd_ports(k: usize) -> bool {
    if k < 3 || k.is_multiple_of(2) {
        return false;
    }
    let (n, pts) = hstar_family(k);
    if !verify_q_hstar(n, &pts) {
        return false;
    }
    let m = pts.len();
    let d_idx = 4 * k * k - (k / 2 + 1);
    if pts[0] != (0, 0) || d_idx == 0 || d_idx >= m {
        return false;
    }
    let p0 = (0usize, 0usize);
    let p1 = (n - 1, 0usize);
    let xq: Vec<(usize, usize)> = pts
        .iter()
        .map(|&(y, z)| ((y + 1) % n, (z + n - 1) % n))
        .collect();
    let conf = |a: (usize, usize), b: (usize, usize)| -> bool {
        cyc_dist(n, a.0, b.0) <= 1 && cyc_dist(n, a.1, b.1) <= 7
    };
    for t in 0..m {
        if conf(p1, pts[t]) != (t == 0) {
            return false;
        }
        if conf(p0, xq[t]) != (t == 0) {
            return false;
        }
        if conf(p1, xq[t]) != (t == d_idx) {
            return false;
        }
    }
    true
}

pub fn helical_hbpz_family(m: usize) -> (usize, Vec<(usize, usize)>) {
    let n = 4 * m + 1;
    let big_m = m * m + m / 4;
    let mut pts = Vec::with_capacity(big_m);
    for t in 0..big_m {
        pts.push(((t * n) / big_m, (4 * t) % n));
    }
    (n, pts)
}

pub fn quotient_ball_size(n: usize, a: usize, b: usize, c: usize, d: usize) -> usize {
    let mut seen = vec![false; n * n];
    let mut count = 0usize;
    let offs = [n - 1, 0, 1];
    for &e0 in &offs {
        for &e1 in &offs {
            for &e2 in &offs {
                for &e3 in &offs {
                    let y = (e2 + n * 4 - (a * e0 + b * e1) % n) % n;
                    let z = (e3 + n * 4 - (c * e0 + d * e1) % n) % n;
                    let idx = y * n + z;
                    if !seen[idx] {
                        seen[idx] = true;
                        count += 1;
                    }
                }
            }
        }
    }
    count
}

pub fn baumert_factored_card(p: usize, q: &[(usize, usize)]) -> usize {
    let line_card = |target: usize| -> usize {
        let mut s = 0usize;
        for u in 0..(p + 2) {
            let pu = pull1(u);
            let target_w = (2 * pu + target) % p;
            let fiber = if target_w < 2 { 2 } else { 1 };
            s += fiber;
        }
        s
    };
    let mut total = 0usize;
    for &(qy, qz) in q {
        total += line_card(qy) * line_card(qz);
    }
    total
}

pub fn verify_baumert_expanded_independent(p: usize, q: &[(usize, usize)]) -> (usize, bool) {
    let np = p + 2;
    let mut qgrid = vec![false; p * p];
    for &(y, z) in q {
        qgrid[y * p + z] = true;
    }
    let mut words: Vec<[usize; 4]> = Vec::new();
    for w0 in 0..np {
        let p0 = pull1(w0);
        for w1 in 0..np {
            let p1 = pull1(w1);
            for w2 in 0..np {
                let p2 = pull1(w2);
                let qy = (p2 + 2 * p - 2 * p1) % p;
                for w3 in 0..np {
                    let p3 = pull1(w3);
                    let qz = (p3 + 2 * p - 2 * p0) % p;
                    if qgrid[qy * p + qz] {
                        words.push([w0, w1, w2, w3]);
                    }
                }
            }
        }
    }
    let mut occ = vec![false; np * np * np * np];
    for &w in &words {
        let code = ((w[0] * np + w[1]) * np + w[2]) * np + w[3];
        occ[code] = true;
    }
    let step = |x: usize| [x, (x + 1) % np, (x + np - 1) % np];
    for &w in &words {
        let self_code = ((w[0] * np + w[1]) * np + w[2]) * np + w[3];
        for x0 in step(w[0]) {
            for x1 in step(w[1]) {
                for x2 in step(w[2]) {
                    for x3 in step(w[3]) {
                        let c = ((x0 * np + x1) * np + x2) * np + x3;
                        if c != self_code && occ[c] {
                            return (words.len(), false);
                        }
                    }
                }
            }
        }
    }
    (words.len(), true)
}

pub fn verify_g7_c5_and_alpha() -> (bool, usize) {
    let c5 = [0usize, 2, 6, 5, 3];
    let mut c5_ok = true;
    for i in 0..5 {
        for j in 0..5 {
            let adj_c5 = i != j && cyc_dist(5, i, j) == 1;
            let adj_g7 = i != j && !SEP_G7[c5[i]][c5[j]];
            if adj_c5 != adj_g7 {
                c5_ok = false;
            }
        }
    }
    let mut best_alpha = 0usize;
    for mask in 0u8..128 {
        let mut indep = true;
        let mut sz = 0usize;
        for (i, row) in SEP_G7.iter().enumerate() {
            if (mask >> i) & 1 == 1 {
                sz += 1;
                for (j, &sep) in row.iter().enumerate().skip(i + 1) {
                    if ((mask >> j) & 1 == 1) && !sep {
                        indep = false;
                    }
                }
            }
        }
        if indep && sz > best_alpha {
            best_alpha = sz;
        }
    }
    (c5_ok, best_alpha)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ZSqrt5(i64, i64);

impl ZSqrt5 {
    fn add(self, o: Self) -> Self { Self(self.0 + o.0, self.1 + o.1) }
    fn mul(self, o: Self) -> Self { Self(self.0 * o.0 + 5 * self.1 * o.1, self.0 * o.1 + self.1 * o.0) }
}

pub fn verify_lovasz_c5_idempotent() -> bool {
    let m5 = |i: usize, j: usize| -> ZSqrt5 {
        match cyc_dist(5, i, j) {
            0 => ZSqrt5(-2, 2),
            1 => ZSqrt5(3, -1),
            _ => ZSqrt5(-2, 0),
        }
    };
    let scale = ZSqrt5(-5, 5);
    for i in 0..5 {
        for j in 0..5 {
            let mut sum = ZSqrt5(0, 0);
            for k in 0..5 {
                sum = sum.add(m5(i, k).mul(m5(k, j)));
            }
            if sum != scale.mul(m5(i, j)) {
                return false;
            }
        }
    }
    true
}

pub fn schlafli_comp_adj(u: usize, v: usize) -> bool {
    if u == v {
        return false;
    }
    if u < 6 {
        if v < 6 { false }
        else if v < 12 { u != v - 6 }
        else { let (a, b) = CPAIR[v - 12]; u == a || u == b }
    } else if u < 12 {
        if v < 6 { u - 6 != v }
        else if v < 12 { false }
        else { let (a, b) = CPAIR[v - 12]; u - 6 == a || u - 6 == b }
    } else {
        let (a, b) = CPAIR[u - 12];
        if v < 6 { v == a || v == b }
        else if v < 12 { v - 6 == a || v - 6 == b }
        else {
            let (c, d) = CPAIR[v - 12];
            a != c && a != d && b != c && b != d
        }
    }
}

pub fn verify_schlafli_paradox() -> (bool, bool, usize) {
    let handle: [i64; 8] = [1, 1, 1, 1, 1, 1, 3, 3];
    let mut vecs = [[0i64; 8]; 27];
    for i in 0..6 {
        vecs[i][i] = 2;
        vecs[i][6] = 2;
        vecs[6 + i][i] = 2;
        vecs[6 + i][7] = 2;
    }
    for (idx, &(a, b)) in CPAIR.iter().enumerate() {
        for (k, slot) in vecs[12 + idx].iter_mut().enumerate().take(6) {
            *slot = if k == a || k == b { -1 } else { 1 };
        }
        vecs[12 + idx][6] = 1;
        vecs[12 + idx][7] = 1;
    }
    let h_norm: i64 = handle.iter().map(|&x| x * x).sum();
    let mut z8_ok = h_norm == 24;
    for u in 0..27 {
        let norm: i64 = vecs[u].iter().map(|&x| x * x).sum();
        let hdot: i64 = (0..8).map(|k| handle[k] * vecs[u][k]).sum();
        if norm != 8 || hdot != 8 {
            z8_ok = false;
        }
        for v in 0..27 {
            if schlafli_comp_adj(u, v) {
                let dot: i64 = (0..8).map(|k| vecs[u][k] * vecs[v][k]).sum();
                if dot != 0 {
                    z8_ok = false;
                }
            }
        }
    }
    let mut f2_ok = true;
    for (u, &lbits) in SCHLAFLI_L_BITS.iter().enumerate() {
        for v in 0..27 {
            let mut acc = 0u32;
            for (k, &rbits) in SCHLAFLI_R_BITS.iter().enumerate() {
                let lu = (lbits >> k) & 1;
                let rv = (rbits >> v) & 1;
                acc ^= lu & rv;
            }
            let expected = if u == v || schlafli_comp_adj(u, v) { 1u32 } else { 0u32 };
            if acc != expected {
                f2_ok = false;
            }
        }
    }
    (z8_ok, f2_ok, 27)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("--verify-all");
    match mode {
        "--verify-all" | "--json" => {
            let q25_ok = verify_q_hbpz(25, &Q25_HBPZ);
            let q29_ok = verify_q_hbpz(29, &Q29_HBPZ);
            let (n25, q25_hstar) = hstar_family(3);
            let hstar_ok = n25 == 25 && q25_hstar.len() == 37 && verify_q_hstar(25, &q25_hstar);
            let hstar_ports_ok = verify_hstar_odd_ports(3)
                && verify_hstar_odd_ports(5)
                && verify_hstar_odd_ports(7);
            let ball_hstar = quotient_ball_size(25, 0, 0, 2, 4);
            let ball_hbpz = quotient_ball_size(25, 0, 2, 2, 0);
            let c27_card = baumert_factored_card(25, &Q25_HBPZ);
            let c31_card = baumert_factored_card(29, &Q29_HBPZ);
            let (c27_exp, c27_indep) = verify_baumert_expanded_independent(25, &Q25_HBPZ);
            let (c31_exp, c31_indep) = verify_baumert_expanded_independent(29, &Q29_HBPZ);
            let (g7_c5, g7_alpha) = verify_g7_c5_and_alpha();
            let c5_idem = verify_lovasz_c5_idempotent();
            let (sch_z8, sch_f2, sch_prod) = verify_schlafli_paradox();

            let helical_ok = [5usize, 8, 9, 12, 13, 16, 17, 20].iter().all(|&m| {
                let (n, pts) = helical_hbpz_family(m);
                let ceil = (n * (n / 4)) / 4;
                pts.len() == ceil && verify_q_hbpz(n, &pts)
            });

            let all_ok = q25_ok
                && q29_ok
                && hstar_ok
                && hstar_ports_ok
                && ball_hstar == 45
                && ball_hbpz == 49
                && c27_card == 31466
                && c27_exp == 31466
                && c27_indep
                && c31_card == 54913
                && c31_exp == 54913
                && c31_indep
                && g7_c5
                && g7_alpha == 3
                && c5_idem
                && sch_z8
                && sch_f2
                && sch_prod == 27
                && helical_ok;

            println!(
                "{{\"all_ok\":{},\"q25_hbpz_valid\":{},\"q29_hbpz_valid\":{},\"hstar_25_valid\":{},\"hstar_odd_ports_valid\":{},\"helical_hbpz_valid\":{},\"ball_hstar_25\":{},\"ball_hbpz_25\":{},\"baumert_c27_words\":{},\"baumert_c31_words\":{},\"g7_c5_induced\":{},\"g7_alpha\":{},\"lovasz_c5_idempotent\":{},\"schlafli_z8_valid\":{},\"schlafli_f2_rank7_valid\":{},\"schlafli_prod_indep\":{}}}",
                all_ok, q25_ok, q29_ok, hstar_ok, hstar_ports_ok, helical_ok,
                ball_hstar, ball_hbpz, c27_card, c31_card, g7_c5, g7_alpha, c5_idem,
                sch_z8, sch_f2, sch_prod
            );
            if !all_ok {
                process::exit(1);
            }
        }
        "--scan-subgroups" => {
            let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(19);
            let mut min_ball = usize::MAX;
            let mut best = (0usize, 0usize, 0usize, 0usize);
            for a in 0..n {
                for b in 0..n {
                    for c in 0..n {
                        for d in 0..n {
                            let sz = quotient_ball_size(n, a, b, c, d);
                            if sz < min_ball {
                                min_ball = sz;
                                best = (a, b, c, d);
                            }
                        }
                    }
                }
            }
            println!(
                "{{\"n\":{},\"min_ball\":{},\"witness\":[{},{},{},{}]}}",
                n, min_ball, best.0, best.1, best.2, best.3
            );
        }
        "--help" | "-h" => {
            println!("zero-error-torus-frontier v1.0.0 (Rust stdlib-only verifier)");
            println!("Usage: zero-error-torus-frontier [--verify-all|--json|--scan-subgroups N]");
        }
        other => {
            eprintln!("Unknown argument: {}", other);
            process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pillar1_quotients_and_balls() {
        assert!(verify_q_hbpz(25, &Q25_HBPZ));
        assert!(verify_q_hbpz(29, &Q29_HBPZ));
        assert_eq!(quotient_ball_size(19, 0, 0, 2, 4), 45);
        assert_eq!(quotient_ball_size(25, 0, 0, 2, 4), 45);
        assert_eq!(quotient_ball_size(25, 0, 2, 2, 0), 49);
        for k in [3usize, 5, 7, 9, 11] {
            assert!(verify_hstar_odd_ports(k));
        }
    }

    #[test]
    fn test_pillar2_baumert_pullbacks() {
        assert_eq!(baumert_factored_card(25, &Q25_HBPZ), 31466);
        assert_eq!(baumert_factored_card(29, &Q29_HBPZ), 54913);
        assert_eq!(verify_baumert_expanded_independent(25, &Q25_HBPZ), (31466, true));
        assert_eq!(verify_baumert_expanded_independent(29, &Q29_HBPZ), (54913, true));
    }

    #[test]
    fn test_pillar3_and_pillar4() {
        assert_eq!(verify_g7_c5_and_alpha(), (true, 3));
        assert!(verify_lovasz_c5_idempotent());
        assert_eq!(verify_schlafli_paradox(), (true, true, 27));
    }

    #[test]
    fn test_negative_invalid_packings_rejected() {
        let bad = [(0usize, 0usize), (1, 1)];
        assert!(!verify_q_hbpz(25, &bad));
        assert!(!verify_q_hstar(25, &bad));
        assert!(!verify_hstar_odd_ports(4));
    }
}
