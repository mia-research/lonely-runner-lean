"""
De-risk: (4,2) c=1 branch of bhk_prop11_exc_open / core_q18.

Relation q | 2(r-2p); c=1 means 2(r-2p)=q, so q even, r = 2p + q/2,
constraints (from q<r<3q/2, 3p<q, gcd(p,q)=1): q/4 < p < q/3, p odd, q even.
This branch appears in core_q18 (q>=30) but NOT in core2 (6p<q kills q/4<p).

Fold: Y = {p/q (l+1/2)}, X = {r/q (l+1/2)}. r/q = 2p/q + 1/2.
  r/q (l+1/2) = 2 (p/q)(l+1/2) + (1/2)(l+1/2) = 2*(intpart+Y) + l/2 + 1/4.
  l ODD = 2m+1: l/2 = m + 1/2 -> X = {2Y + 1/2 + 1/4} = {2Y + 3/4} = 2Y - 1/4  (needs Y>=1/8).
  l EVEN: X = {2Y + 1/4} = 2Y + 1/4 (window <1/q, unusable) -> use ODD l only.

Y-grid over odd l: l=2m+1 -> Y = {m*(2p/q) + 3p/(2q)}. With q=2q', generator p/q'
coprime, spacing 1/q' = 2/q. So any Y-window of width >= 2/q is guaranteed a hit.

Pentagon (pent_no_good_red) 6 conditions with M=(s-q)/(3qs), X=2Y-1/4:
  h39 : X >= 1/6 - r*M
  h40 : Y >= 1/6 - p*M
  h41 : Y <= 1/3 + (q-p)*M
  hxle: X <= 5/6
  h42a: 1/(3s) <= (5/6 - X)/r + (Y - 1/6)/p
  h42b: 1/(3s) <= (5/6 - X)/r + (1/3 - Y)/(q-p)
plus fold validity Y >= 1/8.

A cone point ({X},{Y}) in the pentagon contradicts C∩P=∅, killing the config.
We need: for EVERY valid (p,q,r) and EVERY s>r, the feasible Y-interval has
width >= 2/q (so the odd-l grid lands a point). Report any failure.
"""
from math import gcd
from fractions import Fraction as F

def feasible_Y_window(p, q, r, s):
    """Return (L, U) feasible Y interval from the 6 pentagon conds + fold, X=2Y-1/4."""
    M = F(s - q, 3 * q * s)
    # X = 2Y - 1/4
    # h39: 2Y-1/4 >= 1/6 - r M  -> Y >= (1/6 - rM + 1/4)/2 = (5/12 - rM)/2
    L1 = (F(5, 12) - r * M) / 2
    # h40: Y >= 1/6 - p M
    L2 = F(1, 6) - p * M
    # fold validity
    L3 = F(1, 8)
    # h41: Y <= 1/3 + (q-p) M
    U1 = F(1, 3) + (q - p) * M
    # hxle: 2Y-1/4 <= 5/6 -> Y <= 13/24
    U2 = F(13, 24)
    # h42a: (Y-1/6)/p + (5/6 - X)/r >= 1/(3s); X=2Y-1/4 -> (5/6-X)/r = (13/12 - 2Y)/r
    #   (1/p - 2/r) Y >= 1/(3s) + 1/(6p) - 13/(12 r)
    a = F(1, p) - F(2, r)            # coeff of Y (should be > 0)
    rhs_a = F(1, 3 * s) + F(1, 6 * p) - F(13, 12 * r)
    # h42b: (1/3-Y)/(q-p) + (13/12-2Y)/r >= 1/(3s)
    #   (-1/(q-p) - 2/r) Y >= 1/(3s) - 1/(3(q-p)) - 13/(12 r)
    b = -F(1, q - p) - F(2, r)       # coeff of Y (< 0)
    rhs_b = F(1, 3 * s) - F(1, 3 * (q - p)) - F(13, 12 * r)
    L4 = rhs_a / a if a > 0 else F(-10)   # lower bound (a>0)
    U3 = rhs_b / b if b < 0 else F(10)    # upper bound (b<0, dividing flips)
    L = max(L1, L2, L3, L4)
    U = min(U1, U2, U3)
    return L, U

def valid_triples(qmax):
    out = []
    for q in range(30, qmax + 1, 2):          # q even, q>=30
        lo = q // 4 + 1
        hi = (q - 1) // 3
        for p in range(lo, hi + 1):
            if p % 2 == 0:        # p must be odd (coprime to even q)
                continue
            if gcd(p, q) != 1:
                continue
            r = 2 * p + q // 2
            if not (q < r and 2 * r < 3 * q):
                continue
            out.append((p, q, r))
    return out

def main():
    qmax = 400
    triples = valid_triples(qmax)
    print(f"valid c=1 triples q in [30,{qmax}]: {len(triples)}")
    fails = 0
    worst_margin = None   # min over all of (width - 2/q) in units of (2/q)
    n_checked = 0
    examples = []
    for (p, q, r) in triples:
        spacing = F(2, q)
        # s ranges over r+1 .. large; also include far s. Worst case search.
        s_list = list(range(r + 1, r + 1 + 12 * q))
        for s in s_list:
            L, U = feasible_Y_window(p, q, r, s)
            width = U - L
            n_checked += 1
            ratio = width / spacing
            if width < spacing:
                fails += 1
                if len(examples) < 12:
                    examples.append((p, q, r, s, float(width), float(spacing), float(ratio)))
            if worst_margin is None or ratio < worst_margin[0]:
                worst_margin = (ratio, p, q, r, s, float(width), float(spacing))
    print(f"checked {n_checked} (triple,s) pairs")
    print(f"FAILURES (width < 2/q): {fails}")
    if examples:
        print("examples of failure (p,q,r,s,width,spacing,ratio):")
        for e in examples:
            print("  ", e)
    wm = worst_margin
    print(f"worst width/spacing ratio = {float(wm[0]):.4f} at p,q,r,s={wm[1:5]} "
          f"(width={wm[5]:.5f}, spacing={wm[6]:.5f})")

if __name__ == "__main__":
    main()
