"""
De-risk v2: the EXPLICIT two-regime window the Lean proof of (4,2) c=1 will use.

Mirrors bhk_prop11_exc_2_1_pentkill, split on rM <=> 1/6  (M=(s-q)/(3qs)):
  Regime A (rM <= 1/6): window_lo = 5/24 - rM/2,  len = 2/q
  Regime B (rM >  1/6): window_lo = 1/8,          len = 2/q
The odd-l grid (spacing 2/q) lands a point Y in [lo, lo+2/q]. For the kill to go
through, EVERY Y in [lo, lo+2/q] must satisfy all 6 pentagon conditions with
X = 2Y - 1/4. Conditions are monotone/linear in Y so endpoints suffice; we test
a fine sweep of Y across the interval to be safe.
"""
from math import gcd
from fractions import Fraction as F

def conds_ok(Y, p, q, r, s):
    M = F(s - q, 3 * q * s)
    X = 2 * Y - F(1, 4)
    h39 = X >= F(1, 6) - r * M
    h40 = Y >= F(1, 6) - p * M
    h41 = Y <= F(1, 3) + (q - p) * M
    hxle = X <= F(5, 6)
    hfold = (Y >= F(1, 8)) and (X >= 0) and (X < 1)
    h42a = F(1, 3 * s) <= (F(5, 6) - X) / r + (Y - F(1, 6)) / p
    h42b = F(1, 3 * s) <= (F(5, 6) - X) / r + (F(1, 3) - Y) / (q - p)
    return all([h39, h40, h41, hxle, hfold, h42a, h42b])

def window(p, q, r, s):
    M = F(s - q, 3 * q * s)
    rM = r * M
    if rM <= F(1, 6):
        lo = F(5, 24) - rM / 2          # regime A
    else:
        lo = F(1, 8)                    # regime B
    return lo, lo + F(2, q)

def valid_triples(qmax):
    out = []
    for q in range(30, qmax + 1, 2):
        for p in range(q // 4 + 1, (q - 1) // 3 + 1):
            if p % 2 == 0 or gcd(p, q) != 1:
                continue
            r = 2 * p + q // 2
            if q < r and 2 * r < 3 * q:
                out.append((p, q, r))
    return out

def main():
    qmax = 400
    triples = valid_triples(qmax)
    print(f"valid c=1 triples: {len(triples)}")
    fails = []
    n = 0
    NPT = 9   # sample points across [lo, lo+2/q]
    for (p, q, r) in triples:
        for s in range(r + 1, r + 1 + 12 * q):
            lo, hi = window(p, q, r, s)
            n += 1
            for k in range(NPT + 1):
                Y = lo + (hi - lo) * F(k, NPT)
                if not conds_ok(Y, p, q, r, s):
                    fails.append((p, q, r, s, float(Y), k))
                    break
    print(f"checked {n} (triple,s) windows x {NPT+1} pts")
    print(f"FAILURES: {len(fails)}")
    for e in fails[:15]:
        print("  ", e)

if __name__ == "__main__":
    main()
