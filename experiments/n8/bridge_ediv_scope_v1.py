"""
bridge_ediv_scope_v1.py -- n=8.  Two things:

 (A) HAND-CHECKABLE VERIFICATION of the two specific counterexamples quoted in the
     report, recomputed from the definitions with every intermediate printed.

 (B) SCOPE: for which E_div is the E_non-only reading of "safe fibre" (sections 2
     and 2.4) actually sufficient for the map k = b + r*L?  Partition tuples by
     E_div and measure.

Exact integer arithmetic.
"""

from math import gcd, lcm
from itertools import combinations

n = 8
FULL = set(range(n))


def sol(e, j):
    return {r for r in range(n) if (e * r) % n == j % n}


def bad_set(e, t):
    return sol(e, -t) | sol(e, -(t + 1))


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


def show(E, L, b, target, label):
    print(f"\n  [{label}]  E = {E},  L = lcm(E) = {lcm(*E)} (stated {L}),  "
          f"gcd = {__import__('math').gcd(*[gcd(E[0],x) for x in E]) if False else 0}")
    g = 0
    for x in E:
        g = gcd(g, x)
    print(f"     gcd(E) = {g};  E_div = {[e for e in E if e%n==0]};  "
          f"R_non = {sorted({e%n for e in E if e%n!=0})}")
    print(f"     fibre b = {b};  B_div = [{L//n}, {(n-1)*L//n}];  "
          f"b in B_div: {L//n <= b <= (n-1)*L//n}")
    print(f"     target residue = {target}")
    for e in E:
        t = (e * b) // L
        bs = sorted(bad_set(e, t))
        mark = "  <-- COVERS TARGET" if target in bad_set(e, t) else ""
        print(f"       e={e:4d} (gcd(e,8)={gcd(e,n)}, {'div' if e%n==0 else 'non'}) "
              f"t=floor({e}*{b}/{L})={t:4d}  bad={bs}{mark}")
    un_non, un_all = cover(E, b, L)
    print(f"     uncovered by E_non : {sorted(FULL-un_non)}")
    print(f"     uncovered by all E : {sorted(FULL-un_all)}")
    k = b + target * L
    N = n * L
    print(f"     k = b + r*L = {k};  N = {N};  positions (e*k mod N), safe band "
          f"[{L},{(n-1)*L}]:")
    for e in E:
        p = (e * k) % N
        print(f"       e={e:4d}  {e}*{k} mod {N} = {p:7d}   "
              f"{'IN' if L <= p <= (n-1)*L else 'OUT  <-- k is NOT a safe point'}")
    print(f"     => k is a safe point: {is_safe_k(E, k, L)}")


def scope(Lmax, cap):
    buckets = {}
    for L in range(n, Lmax + 1, n):
        for E in tuples_with_lcm(L, cap=cap):
            Ediv = tuple(e for e in E if e % n == 0)
            key = "E_div == {8} exactly" if Ediv == (8,) else (
                  "|E_div| == 1, e_div != 8" if len(Ediv) == 1 else "|E_div| >= 2")
            d = buckets.setdefault(key, dict(tuples=0, fibres=0, barren=0,
                                             pairs=0, pairfail=0, endpoint_only=0))
            d["tuples"] += 1
            blo, bhi = L // n, (n - 1) * L // n
            for b in range(blo, bhi + 1):
                un_non, _ = cover(E, b, L)
                if un_non == FULL:
                    continue
                d["fibres"] += 1
                rs = sorted(FULL - un_non)
                good = 0
                for r in rs:
                    d["pairs"] += 1
                    if is_safe_k(E, b + r * L, L):
                        good += 1
                    else:
                        d["pairfail"] += 1
                if good == 0:
                    d["barren"] += 1
                    if b == bhi:
                        d["endpoint_only"] += 1
    return buckets


if __name__ == "__main__":
    print("=== (A) the two counterexamples, recomputed from the definitions ===")
    show((1, 2, 3, 4, 6, 8, 24), 24, 6, 1,
         "Lemma 11.3c: n=8 even, d=7 dropped unit, r_d = -d^{-1} = 1, "
         "b_early = 2L/n = 6")
    show((1, 2, 3, 4, 5, 6, 64), 960, 839, 6,
         "Lemma 11.3a' Case III (e_div = 64 = 8*8, k = 8 = 0 mod 8; every "
         "non-divisible speed < 8 so q_e = 0), d=7, s_d = d^{-1}-1 = 6, "
         "witness b* - 1 = 839")

    print("\n\n=== (B) scope of the E_non-only reading of 'safe fibre' ===")
    for key, d in sorted(scope(1200, 10).items()):
        print(f"\n  {key}")
        print(f"    tuples                                     : {d['tuples']}")
        print(f"    E_non-safe fibres                          : {d['fibres']}")
        print(f"    ... barren (no uncovered r gives a safe k)  : {d['barren']}"
              f"  ({100.0*d['barren']/max(d['fibres'],1):.2f}%)")
        print(f"    ... of those, at the right endpoint b=(n-1)L/n: {d['endpoint_only']}")
        print(f"    (b,r) pairs                                : {d['pairs']}"
              f"   failing the map: {d['pairfail']}"
              f"  ({100.0*d['pairfail']/max(d['pairs'],1):.2f}%)")
