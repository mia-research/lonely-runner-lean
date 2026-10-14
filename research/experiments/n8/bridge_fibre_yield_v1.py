"""
bridge_fibre_yield_v1.py -- n=8.

Two questions the top-level report turns on:

 Q1  Does EVERY safe fibre yield an explicit safe point k?
     Per fibre b that is safe (E_non-only reading, sections 2/2.4), does at least
     one uncovered residue r give a safe k = b + r*L?

 Q2  Lemma 11.3a' (line 866) split by its OWN case hypotheses, so that a failure
     at the manuscript's fixed witness fibre is only counted where the manuscript
     claims that fibre works without a further shift:
       Case I  : e_div = k*n with k != 1, 0 mod n, witness b* = (n-1)L/n.
                 The proof's clean branch also assumes q_e = 0 for every
                 non-divisible runner (i.e. every e in E_non is < n).
       Case II : k = 1 mod n, witness b*-1; proof again computes unit floors
                 assuming q_e = 0.
       Case III: k = 0 mod n, witness b*-1, same.
       The q_e >= 1 branch of the proof does NOT claim b* works; it prescribes a
       leftward shift.  It is reported separately and NOT counted as a refutation.

Exact integer arithmetic.
"""

from math import gcd, lcm
from itertools import combinations

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


def q1(Lmax, cap):
    tot_f = barren_f = 0          # fibres, and fibres yielding no safe k
    tot_t = tup_with_barren = 0
    ex = []
    for L in range(n, Lmax + 1, n):
        for E in tuples_with_lcm(L, cap=cap):
            tot_t += 1
            blo, bhi = L // n, (n - 1) * L // n
            barren_here = 0
            for b in range(blo, bhi + 1):
                un_non, _ = cover(E, b, L)
                if un_non == FULL:
                    continue
                tot_f += 1
                rs = sorted(FULL - un_non)
                if not any(is_safe_k(E, b + r * L, L) for r in rs):
                    barren_f += 1
                    barren_here += 1
                    if len(ex) < 6:
                        _, un_all = cover(E, b, L)
                        ex.append((E, L, b, rs, sorted(FULL - un_all)))
            if barren_here:
                tup_with_barren += 1
    return tot_t, tot_f, barren_f, tup_with_barren, ex


def q2(Lmax, cap):
    res = {}
    for tag in ("I", "II", "III"):
        for q in ("q0", "qpos"):
            res[(tag, q)] = dict(cases=0, cov_non=0, cov_all=0, kbad=0, ex=[])
    for L in range(n, Lmax + 1, n):
        for E in tuples_with_lcm(L, cap=cap):
            Ediv = [e for e in E if e % n == 0]
            if len(Ediv) != 1:
                continue
            kk = Ediv[0] // n
            Enon = [e for e in E if e % n != 0]
            qtag = "q0" if all(e < n for e in Enon) else "qpos"
            bstar = (n - 1) * L // n
            if kk % n == 1:
                tag, b = "II", bstar - 1
            elif kk % n == 0:
                tag, b = "III", bstar - 1
            else:
                tag, b = "I", bstar
            for d in dropped_units(E):
                sd = (inv(d) - 1) % n
                un_non, un_all = cover(E, b, L)
                r = res[(tag, qtag)]
                r["cases"] += 1
                if sd in un_non:
                    r["cov_non"] += 1
                if sd in un_all:
                    r["cov_all"] += 1
                if not is_safe_k(E, b + sd * L, L):
                    r["kbad"] += 1
                    if len(r["ex"]) < 3:
                        r["ex"].append((E, L, d, sd, b, sorted(FULL - un_all)))
    return res


if __name__ == "__main__":
    LMAX, CAP = 1200, 10
    print(f"n=8, L multiple of 8 up to {LMAX}, <= {CAP} tuples per L "
          f"(7 distinct divisors of L, lcm = L, gcd 1, >=1 multiple of 8).\n")

    tt, tf, bf, twb, ex = q1(LMAX, CAP)
    print("Q1  Does every E_non-safe fibre yield a safe point via k = b + r*L?")
    print(f"    tuples                                        : {tt}")
    print(f"    E_non-safe fibres b in B_div                  : {tf}")
    print(f"    ... of which yield NO safe k at all           : {bf}"
          f"  ({100.0*bf/max(tf,1):.1f}%)")
    print(f"    tuples having at least one such barren fibre  : {twb}"
          f"  ({100.0*twb/max(tt,1):.1f}%)")
    for E, L, b, rs, missall in ex:
        print(f"      ex E={E} L={L} b={b} uncovered(E_non)={rs} "
              f"uncovered(all E)={missall} -> every k=b+rL unsafe")

    print("\nQ2  Lemma 11.3a' at its own witness fibre, |E_div| = 1, split by case "
          "and by whether every non-divisible speed is < n (q_e = 0):")
    res = q2(LMAX, CAP)
    for tag in ("I", "II", "III"):
        for q in ("q0", "qpos"):
            r = res[(tag, q)]
            note = "  [proof's clean branch]" if q == "q0" else \
                   "  [proof prescribes a SHIFT here; not a refutation]"
            print(f"    Case {tag:3s} {q:4s} cases={r['cases']:5d}  s_d covered by E_non={r['cov_non']:5d}"
                  f"  by all E={r['cov_all']:5d}  k unsafe={r['kbad']:5d}{note}")
            for E, L, d, sd, b, m in r["ex"][:2]:
                print(f"        ex E={E} L={L} d={d} s_d={sd} b={b} uncovered(all E)={m}")
