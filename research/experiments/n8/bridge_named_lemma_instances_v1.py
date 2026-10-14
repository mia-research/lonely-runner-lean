"""
bridge_named_lemma_instances_v1.py -- n=8 object-level test of the NAMED
manuscript lemmas that instantiate the safe-fibre -> x_0 bridge.

Targets (lrc_proof_v10_21.md):

  L11.3c  Lemma 11.3c (Even-n early-fibre lemma; "proved"), line 909:
          b_early := 2L/n is safe: no retained runner covers r_d = -d^{-1} mod n,
          for d a dropped unit residue class.

  L11.3a' Lemma 11.3a' (Actual-Speed Late-Window Lemma; "proved for composite n"),
          line 866: at b* = (n-1)L/n (or b*-1 in Cases II/III), s_d = d^{-1}-1 mod n
          is uncovered by EVERY retained runner, "giving x_0(E) >= 1".

  P11.3-2 Proposition 11.3-FINAL, Tier 2 Route 2, line 862, the *only* explicit
          n=8 numeric claim in the manuscript:
            "Case n=8, L=120: J = [720/7,105], so J n Z = {103,104,105}
             (3 fibres, all safe by Lemma 11.3a) ... Lemma 11.3c gives the
             additional safe fibre b_early = 2L/n = 30 ... giving x_0 >= 4."

Everything exact integer arithmetic.
"""

from math import gcd, lcm
from itertools import combinations
import numpy as np

n = 8


def bad_set(e, t):
    out = set()
    for j in (-t, -(t + 1)):
        jj = j % n
        out |= {r for r in range(n) if (e * r) % n == jj}
    return out


def cover(E, b, L):
    """union of bad sets at fibre b, returned as (E_non-only, all-E)."""
    un_non, un_all = set(), set()
    for e in E:
        s = bad_set(e, (e * b) // L)
        un_all |= s
        if e % n != 0:
            un_non |= s
    return un_non, un_all


def is_safe_k(E, k, L):
    N = n * L
    return all(L <= (e * k) % N <= (n - 1) * L for e in E)


def x0_of(E, L):
    N = n * L
    k = np.arange(1, N, dtype=np.int64)
    ok = np.ones(N - 1, dtype=bool)
    for e in E:
        p = (np.int64(e) * k) % N
        ok &= (p >= L) & (p <= (n - 1) * L)
    return int(ok.sum()), k[ok]


def tuples_with_lcm(L, cap=None):
    divs = [d for d in range(1, L + 1) if L % d == 0]
    out = []
    for c in combinations(divs, 7):
        if not any(x % n == 0 for x in c):
            continue
        g = 0
        for x in c:
            g = gcd(g, x)
        if g != 1:
            continue
        l = 1
        for x in c:
            l = lcm(l, x)
        if l != L:
            continue
        out.append(c)
        if cap and len(out) >= cap:
            break
    return out


def dropped_units(E):
    R = {e % n for e in E if e % n != 0}
    return [d for d in (1, 3, 5, 7) if d not in R]


def inv(d):
    return next(x for x in range(1, n) if (d * x) % n == 1)


# ------------------------------------------------------------ L11.3c and L11.3a'
def run_named(Lmax=1200):
    stats = dict(c_cases=0, c_fibre_unsafe_all=0, c_rd_covered_non=0, c_rd_covered_all=0,
                 c_k_bad=0,
                 a_cases=0, a_sd_covered_non=0, a_sd_covered_all=0, a_k_bad=0,
                 a2_sd_covered_all=0, a2_k_bad=0)
    ex = {"c": [], "a": []}
    for L in range(n, Lmax + 1, n):
        for E in tuples_with_lcm(L, cap=8):
            du = dropped_units(E)
            if not du:
                continue
            for d in du:
                rd = (-inv(d)) % n
                sd = (inv(d) - 1) % n

                # ---- Lemma 11.3c : b_early = 2L/n
                b_e = 2 * L // n
                un_non, un_all = cover(E, b_e, L)
                stats["c_cases"] += 1
                if un_all == set(range(n)):
                    stats["c_fibre_unsafe_all"] += 1
                if rd in un_non:
                    stats["c_rd_covered_non"] += 1
                if rd in un_all:
                    stats["c_rd_covered_all"] += 1
                    if len(ex["c"]) < 5:
                        ex["c"].append((E, L, d, rd, b_e, sorted(un_all)))
                k = b_e + rd * L
                if not is_safe_k(E, k, L):
                    stats["c_k_bad"] += 1

                # ---- Lemma 11.3a' : b* = (n-1)L/n, and fallback b*-1
                bs = (n - 1) * L // n
                un_non2, un_all2 = cover(E, bs, L)
                stats["a_cases"] += 1
                if sd in un_non2:
                    stats["a_sd_covered_non"] += 1
                if sd in un_all2:
                    stats["a_sd_covered_all"] += 1
                    if len(ex["a"]) < 5:
                        ex["a"].append((E, L, d, sd, bs, sorted(un_all2)))
                k2 = bs + sd * L
                if not is_safe_k(E, k2, L):
                    stats["a_k_bad"] += 1
                # fallback fibre b*-1 (manuscript Cases II / III)
                _, un_all3 = cover(E, bs - 1, L)
                if sd in un_all3:
                    stats["a2_sd_covered_all"] += 1
                k3 = (bs - 1) + sd * L
                if not is_safe_k(E, k3, L):
                    stats["a2_k_bad"] += 1
    return stats, ex


# ------------------------------------------------------------ the L=120 claim
def run_L120():
    L = 120
    Es = tuples_with_lcm(L)
    rows = []
    for E in Es:
        du = dropped_units(E)
        if not du:
            continue
        x0, ks = x0_of(E, L)
        rec = dict(E=E, x0=x0, dropped=du)
        for b in (103, 104, 105, 30):
            un_non, un_all = cover(E, b, L)
            rec[f"b{b}_safe_non"] = un_non != set(range(n))
            rec[f"b{b}_safe_all"] = un_all != set(range(n))
            rec[f"b{b}_miss_all"] = sorted(set(range(n)) - un_all)
        # the manuscript's four claimed witnesses, mapped by k = b + r*L
        wits = []
        for d in du:
            rd = (-inv(d)) % n
            sd = (inv(d) - 1) % n
            for b, r, tag in ((30, rd, "11.3c b_early"), (105, sd, "11.3a' b*"),
                              (104, sd, "J"), (103, sd, "J")):
                wits.append((tag, b, r, b + r * L, is_safe_k(E, b + r * L, L)))
        rec["wit"] = wits
        rows.append(rec)
    return rows


if __name__ == "__main__":
    st, ex = run_named(1200)
    print("=== named-lemma instance test, n=8, all tuples with lcm L <= 1200 "
          "(<=8 per L), every dropped unit class d ===")
    print(f"Lemma 11.3c (b_early = 2L/n, target r_d = -d^-1):")
    print(f"   cases                                    : {st['c_cases']}")
    print(f"   r_d COVERED by some e in E_non (lemma false): {st['c_rd_covered_non']}")
    print(f"   r_d COVERED by some e in E (all)           : {st['c_rd_covered_all']}")
    print(f"   fibre b_early fully covered by all of E    : {st['c_fibre_unsafe_all']}")
    print(f"   k = b_early + r_d*L is NOT a safe point    : {st['c_k_bad']}")
    for e in ex["c"]:
        print(f"     ex E={e[0]} L={e[1]} d={e[2]} r_d={e[3]} b={e[4]} covered={e[5]}")
    print(f"Lemma 11.3a' (b* = (n-1)L/n, target s_d = d^-1 - 1):")
    print(f"   cases                                    : {st['a_cases']}")
    print(f"   s_d COVERED by some e in E_non             : {st['a_sd_covered_non']}")
    print(f"   s_d COVERED by some e in E (all)           : {st['a_sd_covered_all']}")
    print(f"   k = b* + s_d*L is NOT a safe point         : {st['a_k_bad']}")
    print(f"   [fallback b*-1] s_d covered by all of E    : {st['a2_sd_covered_all']}")
    print(f"   [fallback b*-1] k NOT a safe point         : {st['a2_k_bad']}")
    for e in ex["a"]:
        print(f"     ex E={e[0]} L={e[1]} d={e[2]} s_d={e[3]} b={e[4]} covered={e[5]}")

    print("\n=== Proposition 11.3-FINAL Tier-2 Route-2, the explicit n=8, L=120 claim ===")
    rows = run_L120()
    print(f"tuples with lcm exactly 120, some multiple of 8, gcd 1, "
          f"and >=1 dropped unit class: {len(rows)}")
    bad = 0
    for r in rows:
        allsafe = all(r[f"b{b}_safe_all"] for b in (103, 104, 105, 30))
        witbad = [w for w in r["wit"] if not w[4]]
        if not allsafe or witbad or r["x0"] < 4:
            bad += 1
            if bad <= 6:
                print(f"  E={r['E']} x0={r['x0']} dropped={r['dropped']}")
                for b in (103, 104, 105, 30):
                    print(f"     b={b}: safe(E_non)={r[f'b{b}_safe_non']} "
                          f"safe(all E)={r[f'b{b}_safe_all']} "
                          f"uncovered(all E)={r[f'b{b}_miss_all']}")
                for w in r["wit"][:8]:
                    print(f"     witness {w[0]:14s} b={w[1]:3d} r={w[2]} "
                          f"k={w[3]:5d} safe_point={w[4]}")
    print(f"tuples violating some part of the L=120 claim: {bad} / {len(rows)}")
    print(f"min x_0 over these tuples: {min(r['x0'] for r in rows) if rows else 'n/a'}")
