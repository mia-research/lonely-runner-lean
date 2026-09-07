"""
bridge_named_lemma_instances_v2.py -- n=8, careful case-respecting test of the
named lemmas of lrc_proof_v10_21.md that instantiate the bridge, plus the single
explicit n=8 numeric claim in the manuscript.

v2 over v1: each lemma is tested ONLY inside its own stated hypotheses, and the
L=120 claim is broken into its separate components so no failure is attributed
to the wrong clause.  Exact integer arithmetic throughout.
"""

from math import gcd, lcm
from itertools import combinations
import numpy as np

n = 8
FULL = set(range(n))


def bad_set(e, t):
    out = set()
    for j in (-t, -(t + 1)):
        jj = j % n
        out |= {r for r in range(n) if (e * r) % n == jj}
    return out


def cover(E, b, L):
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
    return int(ok.sum())


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


# ---------------------------------------------------------------- Lemma 11.3c
def test_11_3c(Lmax):
    """Lemma 11.3c has NO restriction beyond: n even composite, d a dropped unit
    residue class.  Claim: r_d = -d^{-1} is uncovered at b_early = 2L/n by every
    RETAINED runner."""
    cases = cov_non = cov_all = kbad = fibre_unsafe = 0
    ex = []
    for L in range(n, Lmax + 1, n):
        for E in tuples_with_lcm(L, cap=10):
            for d in dropped_units(E):
                rd = (-inv(d)) % n
                b = 2 * L // n
                un_non, un_all = cover(E, b, L)
                cases += 1
                if rd in un_non:
                    cov_non += 1
                    if len(ex) < 4:
                        blockers = [(e, (e * b) // L, sorted(bad_set(e, (e * b) // L)))
                                    for e in E if e % n != 0
                                    and rd in bad_set(e, (e * b) // L)]
                        ex.append((E, L, d, rd, b, blockers, sorted(FULL - un_all)))
                if rd in un_all:
                    cov_all += 1
                if un_all == FULL:
                    fibre_unsafe += 1
                if not is_safe_k(E, b + rd * L, L):
                    kbad += 1
    return cases, cov_non, cov_all, fibre_unsafe, kbad, ex


# --------------------------------------------------------------- Lemma 11.3a'
def test_11_3a(Lmax):
    """Lemma 11.3a' as written treats ONE divisible runner e_div = k*n, splitting on
    k mod n (Case I: k != 1; Case II: k = 1; Case III: k = 0).  Tested only for
    |E_div| = 1, with the manuscript's own witness fibre for each case; and, per
    the last block of the proof, only Case I additionally requires q_e = 0."""
    res = {}
    for tag in ("I_q0", "I_qpos", "II", "III"):
        res[tag] = dict(cases=0, sd_cov_non=0, sd_cov_all=0, kbad=0, ex=[])
    for L in range(n, Lmax + 1, n):
        for E in tuples_with_lcm(L, cap=10):
            Ediv = [e for e in E if e % n == 0]
            if len(Ediv) != 1:
                continue
            kk = Ediv[0] // n
            Enon = [e for e in E if e % n != 0]
            q0 = all(e < n for e in Enon)
            bstar = (n - 1) * L // n
            if kk % n == 1:
                tag, b = "II", bstar - 1
            elif kk % n == 0:
                tag, b = "III", bstar - 1
            else:
                tag, b = ("I_q0" if q0 else "I_qpos"), bstar
            for d in dropped_units(E):
                sd = (inv(d) - 1) % n
                un_non, un_all = cover(E, b, L)
                r = res[tag]
                r["cases"] += 1
                if sd in un_non:
                    r["sd_cov_non"] += 1
                if sd in un_all:
                    r["sd_cov_all"] += 1
                    if len(r["ex"]) < 3:
                        r["ex"].append((E, L, d, sd, b, sorted(FULL - un_all)))
                if not is_safe_k(E, b + sd * L, L):
                    r["kbad"] += 1
    return res


# ----------------------------------------------- Proposition 11.3-FINAL, L=120
def test_L120():
    L = 120
    tot = 0
    c = dict(b103=0, b104=0, b105=0, b30=0, rd30=0, k30=0, x0lt4=0,
             any_J_all_safe_fail=0)
    ex = []
    for E in tuples_with_lcm(L):
        du = dropped_units(E)
        if not du:
            continue
        tot += 1
        flags = {}
        for b in (103, 104, 105, 30):
            _, un_all = cover(E, b, L)
            flags[b] = (un_all != FULL)
            if not flags[b]:
                c[f"b{b}"] += 1
        if not all(flags[b] for b in (103, 104, 105)):
            c["any_J_all_safe_fail"] += 1
        for d in du:
            rd = (-inv(d)) % n
            _, un_all30 = cover(E, 30, L)
            if rd in un_all30:
                c["rd30"] += 1
            if not is_safe_k(E, 30 + rd * L, L):
                c["k30"] += 1
                if len(ex) < 3:
                    ex.append((E, d, rd, 30 + rd * L, sorted(FULL - un_all30)))
            break   # one dropped class per tuple is enough for the claim
    return tot, c, ex


if __name__ == "__main__":
    LMAX = 1200
    print(f"n = 8.  Tuples: all 7-subsets of divisors of L with lcm exactly L, "
          f"gcd 1, >=1 multiple of 8; L a multiple of 8, L <= {LMAX}; <=10 tuples per L.\n")

    cases, cn, ca, fu, kb, ex = test_11_3c(LMAX)
    print("--- Lemma 11.3c (Even-n early-fibre lemma, line 909, tagged 'proved') ---")
    print(f"  (E,d) cases in scope                              : {cases}")
    print(f"  r_d COVERED at b_early by some RETAINED e in E_non: {cn}"
          f"   <-- direct contradiction of the lemma")
    print(f"  r_d COVERED at b_early by some e in E (all)       : {ca}")
    print(f"  b_early fully covered (not safe even in all-E)    : {fu}")
    print(f"  k = b_early + r_d*L is NOT a safe point           : {kb}")
    for E, L, d, rd, b, blk, miss in ex:
        print(f"    counterexample E={E} L={L} d={d} r_d={rd} b_early={b}")
        for e, t, bs in blk:
            print(f"       blocking retained runner e={e} (gcd(e,8)={gcd(e,8)}) "
                  f"floor t={t} bad={bs}")
        print(f"       fibre's actual uncovered set (all E) = {miss}")

    print("\n--- Lemma 11.3a' (Late-Window Lemma, line 866, tagged 'proved'), |E_div|=1 ---")
    res = test_11_3a(LMAX)
    for tag in ("I_q0", "I_qpos", "II", "III"):
        r = res[tag]
        print(f"  Case {tag:7s} cases={r['cases']:6d}  s_d covered by E_non={r['sd_cov_non']:6d}"
              f"  by all E={r['sd_cov_all']:6d}  k=b+s_d*L unsafe={r['kbad']:6d}")
        for E, L, d, sd, b, miss in r["ex"][:2]:
            print(f"      ex E={E} L={L} d={d} s_d={sd} b={b} uncovered(all E)={miss}")

    print("\n--- Proposition 11.3-FINAL Tier-2 Route-2, explicit n=8 L=120 claim (line 862) ---")
    tot, c, ex = test_L120()
    print(f"  tuples with lcm 120, >=1 multiple of 8, gcd 1, >=1 dropped unit: {tot}")
    for b in (103, 104, 105, 30):
        print(f"  fibre b={b:3d} NOT safe (all-E union = Z/8Z)      : {c[f'b{b}']}")
    print(f"  at least one of 103,104,105 not safe               : {c['any_J_all_safe_fail']}")
    print(f"  r_d covered at b_early=30 (Lemma 11.3c fails here) : {c['rd30']}")
    print(f"  k = 30 + r_d*120 NOT a safe point                  : {c['k30']}")
    for E, d, rd, k, miss in ex:
        print(f"    ex E={E} d={d} r_d={rd} k={k} uncovered at b=30: {miss}")
