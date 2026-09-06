#!/usr/bin/env python3
"""The coarse sector of Rosenfeld's Lemma 7 search, as a covering of Z/p.

SETUP.  k speeds, n = k+1, prime p, N = n*p, targets j in {1..N/2}.
  v covers j  <=>  ||j v / N|| < 1/n  <=>  (j v mod N) < p or > N-p.

COLLAPSE.  If n | v, write v = n*w.  Then j*v mod N = n*(j*w mod p), and
  ||j v / N|| = ||j w / p||,
so v covers j  <=>  (j w mod p) lies in the arc  A = { s : |s|_p <= (p-1)//n }.
Since N/2 = n*p/2 runs over every residue mod p, a set of n-divisible speeds
covers ALL targets  <=>  the dilates { w^{-1} A } cover Z/p.
The object drops from N/2 targets to p residues.

GCD SIDE CONDITION.  A bad cover needs gcd(S u {N}) = 1 for every (k-1)-subset S.
Every n-divisible speed shares the factors of n with N, so at most k-2 of the k
speeds may be n-divisible (two must escape, one for each (k-1)-subset that could
omit the other).  Hence:

  If  f(n,p) := min # dilates of A needed to cover Z/p   satisfies  f(n,p) <= k-2,
  then the coarse sector ALONE yields a bad cover (pad with two escaping speeds)
  and Lemma 7 FAILS at (k,p).

So  f(n,p) >= k-1 = n-2  is NECESSARY for Lemma 7 at (k,p).  This script computes
f(n,p) exactly and tests that necessary condition against the known pattern.

Dilate classes: w and p-w give the same covered set (A is symmetric), and
simultaneous scaling of all w_i is a symmetry of the covering problem.  The
speeds available are v = n*w <= N/2, i.e. w in {1..(p-1)//2} -- which is exactly
one representative of every nonzero +-class.  So the enumeration is complete.
"""
import sys
from itertools import combinations

def arc(n, p):
    h = (p - 1) // n
    return {s % p for s in range(-h, h + 1)}

def masks(n, p):
    """mask[w] = bitset of residues r in Z/p covered by dilate w (i.e. r*w in A)."""
    A = arc(n, p)
    out = {}
    for w in range(1, (p - 1) // 2 + 1):
        m = 0
        for r in range(p):
            if (r * w) % p in A:
                m |= 1 << r
        out[w] = m
    return out

def min_cover(n, p, cap=8):
    """Exact minimum number of dilates covering Z/p; branch on lowest uncovered."""
    M = masks(n, p)
    ws = sorted(M)
    FULL = (1 << p) - 1
    best = [cap + 1]
    witness = [None]

    def rec(chosen, mask):
        if mask == FULL:
            if len(chosen) < best[0]:
                best[0] = len(chosen); witness[0] = list(chosen)
            return
        if len(chosen) + 1 >= best[0]:
            return
        low = (~mask) & FULL
        lb = (low & -low).bit_length() - 1
        for w in ws:
            if w in chosen:
                continue
            if (M[w] >> lb) & 1:
                rec(chosen + [w], mask | M[w])

    rec([], 0)
    return best[0], witness[0]

if __name__ == "__main__":
    print("f(n,p) = min dilates of the arc |s| <= (p-1)//n needed to cover Z/p")
    print("Lemma 7 at (k=n-1, p) REQUIRES f(n,p) >= n-2.\n")
    print(f"{'n':>3} {'k':>3} {'p':>5} {'|A|':>4} {'ceil(p/|A|)':>11} {'f':>3} {'need':>5} {'ok':>4}  witness")
    cases = []
    for n, ps in [(7, [13, 17, 19, 23, 29, 31, 37, 41, 43]),
                  (8, [31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
                       101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163])]:
        for p in ps:
            cases.append((n, p))
    for n, p in cases:
        k = n - 1
        A = arc(n, p)
        f, wit = min_cover(n, p, cap=n - 2)
        need = n - 2
        shown = f if f <= n - 2 else f">{n-2}"
        ok = "FAIL" if (isinstance(f, int) and f <= k - 2) else "ok"
        print(f"{n:>3} {k:>3} {p:>5} {len(A):>4} {-(-p//len(A)):>11} {str(shown):>3} {need:>5} {ok:>4}  {wit}")
        sys.stdout.flush()
