"""
Can a tight n=8 instance have witness denominator q = 8r with r >= 2?
Reduced to an exact minimum-set-cover over Z/8r.  Integer arithmetic only.

SETUP (all proved in docs/n8/HALVING_AND_TIGHT_WITNESS_v1.md sec 3).  T tight at
n = 8 with witness t* = p/q, q = 8r, gcd(p,q) = 1.  Put w_v = v*p mod q.  Then
  (band)      |w_v|_q >= r  for every v in T, where |x|_q = min(x mod q, q - x mod q);
  (extremes)  w = r and w = q-r both occur.
TIGHTNESS forces one more thing, and it is the decidable one: for EVERY c in Z/q the
point t = c/q must fail to beat 1/8, i.e.

    for every c in Z/q there is some v in T with  |c * w_v|_q  <=  r.

Writing Block(w) = { c in Z/q : |c*w|_q <= r }, that says the 7 sets Block(w_v)
COVER Z/q.  So if the minimum number of band residues whose Blocks cover Z/q exceeds
7, no tight instance can have that r -- for that r, r >= 2 is impossible.

This is the same object as the covering problem in docs/n8/COLLAPSE_Z163_v2.md
(f(8,p) = minimum dilates of an arc covering Z/p); here the arc is [-r,r] in Z/8r.

Exact minimum cover by iterative-deepening branch and bound on bitmasks -- no greedy
approximation is reported as an answer.
"""
import sys
from math import gcd

def band_residues(q, r):
    return [w for w in range(1, q) if min(w, q-w) >= r]

def block(w, q, r):
    m = 0
    for c in range(q):
        x = (c*w) % q
        if min(x, q-x) <= r: m |= 1 << c
    return m

def min_cover(q, r, cap=8):
    full = (1 << q) - 1
    sets = sorted({block(w,q,r) for w in band_residues(q,r)},
                  key=lambda m: -bin(m).count("1"))
    # quick feasibility: union of all
    u = 0
    for s in sets: u |= s
    if u != full: return None            # not coverable at all
    for k in range(1, cap+1):
        # branch and bound: always cover the lowest uncovered element
        def rec(cov, depth):
            if cov == full: return True
            if depth == 0: return False
            # lowest uncovered point
            low = (~cov) & full
            c = (low & -low).bit_length() - 1
            for s in sets:
                if s >> c & 1:
                    if rec(cov | s, depth-1): return True
            return False
        if rec(0, k): return k
    return cap+1                          # exceeds cap

def main(rmax):
    print(f"{'r':>3} {'q=8r':>5} {'band':>5} {'min cover of Z/q':>17}  verdict")
    for r in range(1, rmax+1):
        q = 8*r
        b = len(band_residues(q,r))
        k = min_cover(q, r)
        if k is None:
            verdict = "band Blocks do not cover Z/q at all -> r impossible"
        elif k > 7:
            verdict = f"> 7 sets needed -> NO tight instance with r = {r}"
        else:
            verdict = f"{k} <= 7 -> not excluded by this test"
        print(f"{r:>3} {q:>5} {b:>5} {str(k):>17}  {verdict}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv)>1 else 12)
