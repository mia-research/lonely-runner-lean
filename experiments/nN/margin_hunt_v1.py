"""
How close does the procedure come to failing?

The sweeps in EXHAUSTIVE_OTHER_ORDERS_v1 answer "does it return". They do not answer "by
how much". This measures the CLEAR SET -- the part of the window no zone covers -- and
finds, over each exhaustive family, the runner whose clear set is smallest.

WHY THIS IS A DIAGNOSTIC AND NOT A MECHANISM. MANUSCRIPT section 6.1 rules out any argument
that bounds how little the obstructions amount to; it cannot be repaired by measuring more
carefully, because the AP's clear set is a finite set of points. Nothing here is a route to
part 7. The question is different: whether the margin the procedure actually enjoys stays
away from zero over a family, or shrinks as the family grows. Either answer is information
about where part 7 is tightest, and neither is a proof of anything.

THE ALGORITHM IS EXACT AND O(Z log Z).
The zone of reading s = a/b at lap k is the OPEN interval ((nk-1)b/(na), (nk+1)b/(na)).
The clear set is [1/n, (n-1)/n] minus their union; being the complement of finitely many
open intervals in a closed one, its components are closed intervals whose left endpoints lie
in {1/n} u {zone right endpoints} and whose right endpoints lie in {(n-1)/n} u {zone left
endpoints}. Sorting zones by start and sweeping a running maximum of their ends decides
coverage of every candidate in one pass.

Zones are never merged: two zones that touch leave their shared endpoint clear, and the
sweep sees that because coverage of u asks for a zone with a < u < b, strictly.
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd

def readings(v, i, n):
    d = sorted(abs(v[j] - v[i]) for j in range(n) if j != i)
    dmin = d[0]
    return [F(x, dmin) for x in d[1:]]

def zone_list(v, i, n, lo, hi):
    Z = []
    for s in readings(v, i, n):
        k = 0
        while True:
            a = F(n * k - 1, n) / s
            if a > hi:
                break
            b = F(n * k + 1, n) / s
            if b > lo:
                Z.append((a, b))
            k += 1
    return Z

def clear_set(v, i, n):
    """Return (total length of the clear set, a clear point or None)."""
    lo, hi = F(1, n), F(n - 1, n)
    Z = sorted(zone_list(v, i, n, lo, hi))
    # candidate left ends of clear components, and right ends
    starts = sorted({lo} | {b for _, b in Z if lo <= b <= hi})
    ends = sorted({hi} | {a for a, _ in Z if lo <= a <= hi})
    # sweep: u is covered iff max{b : a < u} > u
    def uncovered(cands):
        out, ptr, maxb = [], 0, None
        for u in cands:
            while ptr < len(Z) and Z[ptr][0] < u:
                b = Z[ptr][1]
                if maxb is None or b > maxb:
                    maxb = b
                ptr += 1
            if maxb is None or not (maxb > u):
                out.append(u)
        return out
    us = uncovered(starts)
    if not us:
        return None, None
    # total length: pair each uncovered start with the next uncovered-run end
    ue = uncovered(ends)
    total = F(0)
    j = 0
    for p in us:
        while j < len(ue) and ue[j] < p:
            j += 1
        q = ue[j] if j < len(ue) else p
        if q >= p:
            total += q - p
    return total, us[0]

def sweep(n, V):
    tot = fail = 0
    best = None
    for v in itertools.combinations(range(1, V + 1), n):
        g = 0
        for x in v:
            g = gcd(g, x)
        if g != 1:
            continue
        for i in range(n):
            tot += 1
            m, u = clear_set(list(v), i, n)
            if m is None:
                fail += 1
                print(f"    FAILURE n={n} v={v} runner={i}", flush=True)
                continue
            if best is None or m < best[0]:
                best = (m, v, i, u)
    return tot, fail, best

if __name__ == "__main__":
    print("margin hunt: smallest clear set over each exhaustive family")
    print("n distinct positive integer speeds, gcd 1, no runner pinned at 0; exact\n")
    print(f"{'n':>3} {'V':>4} {'instances':>11} {'fail':>5} {'min clear set':>16} "
          f"{'as frac of window':>18}")
    print("-" * 68)
    spec = [(5, 40), (6, 30), (7, 24), (8, 20), (9, 18), (10, 16)]
    if len(sys.argv) > 1:
        spec = [(int(a.split(':')[0]), int(a.split(':')[1])) for a in sys.argv[1:]]
    for n, V in spec:
        tot, fail, best = sweep(n, V)
        w = F(n - 2, n)
        m, vv, ii, uu = best
        print(f"{n:>3} {V:>4} {tot:>11} {fail:>5} {str(m):>16} {float(m / w):>18.6f}",
              flush=True)
        print(f"        at v={vv} runner={ii}, first clear u={uu}", flush=True)
