#!/usr/bin/env python3
"""Granularity law: per-class coverage arrives in lumps of size gcd(v,n).

The phi(n) AP law (lrc_ap_phi_n_law_v1.md Thm 3.1) and the n=11 paper's Step 3
"equally-spaced preimages" lemma both rest on: j |-> j*r mod n permutes Z/n iff
gcd(r,n) = 1.  Applied to the Rosenfeld/Lemma-7 covering problem it gives an
exact law.

SETUP.  N = n*p, targets j in {1,...,N-1}, v covers j iff j*v mod N < p or > N-p.
Partition targets into the p classes mod p; class r = { r + p*t : t in Z/n }.
Write r*v mod N = a*p + b with 0 <= b < p, so a = block index, b = offset.  Then

    (r + p*t)*v mod N  =  ((a + t*v) mod n)*p + b,

so the block index runs over the coset  a + g*Z/n,  hit g times each, where
g = gcd(v,n).  The covering window is block 0 in full, plus block n-1 minus its
first point (the inequality on that side is strict).  Therefore

    coverage of class r  =  g * |{0} u ({n-1} if b != 0) intersect (a + g*Z/n)|

and b = 0 exactly when p | r.  In particular coverage is always a MULTIPLE OF g:
speeds coprime to n cover at the finest granularity; speeds sharing a factor with
n cover in lumps of size g, and at g = n it is all-or-nothing.

n = 11 is prime, so g = 1 for every admissible speed -- no lumping exists.
n = 8 has four granularity levels, g in {1,2,4,8}.  That is the whole asymmetry.
"""
from math import gcd

def predict(n, p, v, r):
    N = n * p
    g = gcd(v, n)
    rv = (r * v) % N
    a, b = divmod(rv, p)
    win = {0} | ({n - 1} if b != 0 else set())
    coset = {(a + g * s) % n for s in range(n // g)}
    return g * len(win & coset)

def observed(n, p, v, r):
    N = n * p
    return sum(1 for t in range(n)
               if (lambda x: x < p or x > N - p)(((r + p * t) * v) % N))

bad = 0; tot = 0; lumps = {}
for n, ps in [(8, [31, 47, 163]), (11, [13, 23]), (7, [17, 31]), (9, [13])]:
    for p in ps:
        N = n * p
        for v in range(1, N):
            if v % p == 0:
                continue
            g = gcd(v, n)
            for r in range(1, p + 1):
                o = observed(n, p, v, r); e = predict(n, p, v, r)
                tot += 1
                if o != e:
                    bad += 1
                    if bad <= 5:
                        print(f"  MISMATCH n={n} p={p} v={v} r={r}: obs {o} pred {e}")
                lumps.setdefault((n, g), set()).add(o)
print(f"checked {tot} (n,p,v,class) instances;  mismatches: {bad}")
print("\nper-class coverage values seen, by n and g = gcd(v,n):")
for (n, g) in sorted(lumps):
    vals = sorted(lumps[(n, g)])
    ok = all(x % g == 0 for x in vals)
    print(f"  n={n:>2}  g={g:>2}   values {vals}   all multiples of g: {ok}")
