#!/usr/bin/env python3
"""THE ODD-RUNNER COLLAPSE at a >= 4.  Exact Fraction, no float.

In F_2^2 coordinates (chi_1, chi_3) the odd residue blocked by an odd runner is
    g_e = rho_e + bits(q_e),   q_e = floor(4 e t) mod 4,   bits(q) = (q mod 2, q // 2),
and bits(q+1) = bits(q) + (1, q mod 2): the increment DEPENDS on q.  That is the
Klein-vs-cyclic non-homomorphism, and it is what forces a collision.

For t < 1/(2 e^(1)) every odd runner has q_e in {0,1}, with q_e = 1 exactly when
t > 1/(4e).  So as t rises from 0 the set S(t) = {e : q_e = 1} runs through the TOP
SEGMENTS of the odd speeds in decreasing order (those with e > e^(1)/2), and the odd
runners block

    f(S) = { 3*rho_e : e in S }  union  { rho_e : e not in S }        (product in (Z/8)^*)

PART A: is some top segment always non-covering?  Exhaustive over every residue
sequence, a = 4,5,6.  S = {} is the not-Unit-Complete case; S = {largest} is the a = 4
Unit-Complete case (it misses rho^(1), since 3*rho != rho).
PART B: end-to-end on real Case-2 tuples with a >= 4 -- take the collapse interval,
verify the odd runners really do leave a residue free on it, and then see whether the
v2 >= 1 runners also miss it, which produces an actual witness.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd
from functools import reduce
import sys

V = (1, 3, 5, 7)
def mul(x, y): return (x * y) % 8

def nrm(x):
    f = x - int(x); return min(f + 1 if f < 0 else f, 1 - (f + 1 if f < 0 else f))

def blocked(e, t):
    return {j for j in range(8) if nrm(F(e) * (t + F(j, 8))) < F(1, 8)}

def part_A():
    print("PART A -- is some TOP SEGMENT always non-covering?  (exhaustive)")
    for a in (4, 5, 6):
        seqs = tot = failing = 0
        worst_r = 0
        bad = []
        for rho in product(V, repeat=a):          # ordered by DECREASING speed
            seqs += 1
            if set(rho) != set(V):                # not Unit-Complete: S = {} already misses
                continue
            tot += 1
            hit = None
            for r in range(0, a + 1):
                f = {mul(3, rho[i]) for i in range(r)} | {rho[i] for i in range(r, a)}
                if len(f) < 4: hit = r; break
            if hit is None: bad.append(rho)
            else:
                failing += 1
                worst_r = max(worst_r, hit)
        print(f"  a={a}: {tot} Unit-Complete residue sequences; "
              f"some top segment non-covering for {failing}; "
              f"deepest segment needed r = {worst_r}"
              + (f"  COUNTEREXAMPLES {bad[:3]}" if bad else "   (no exceptions)"))
    print()

def part_B(box=18, cap=500):
    print(f"PART B -- end-to-end on Case-2 tuples with a >= 4, box [1..{box}]")
    tuples = [T for T in combinations(range(1, box + 1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)
              and sum(1 for e in T if e % 2) >= 4]
    tuples = tuples[:cap]
    collapse = witness = 0
    for T in tuples:
        odd = sorted([e for e in T if e % 2], reverse=True)
        e1 = odd[0]
        # candidate collapse windows: between consecutive first-jumps, inside t < 1/(2 e1)
        cuts = sorted({F(1, 4 * e) for e in odd if F(1, 4 * e) < F(1, 2 * e1)}
                      | {F(0), F(1, 2 * e1)})
        got_c = got_w = False
        for i in range(len(cuts) - 1):
            lo, hi = cuts[i], cuts[i + 1]
            if lo >= hi: continue
            t = (lo + hi) / 2
            oddhit = set()
            for e in odd: oddhit |= {j for j in blocked(e, t) if j % 2}
            if len(oddhit) == 4: continue
            got_c = True
            rest = set()
            for e in T:
                if e % 2 == 0: rest |= blocked(e, t)
            if not ({1, 3, 5, 7} <= (oddhit | rest)):
                got_w = True
                allhit = oddhit | rest
                for e in odd: allhit |= blocked(e, t)
                assert len(allhit) < 8, f"claimed witness but all blocked: {T} {t}"
                break
        collapse += got_c; witness += got_w
    n = len(tuples)
    print(f"  tuples with a >= 4                                : {n}")
    print(f"  odd runners collapse on a near-0 window           : {collapse} "
          f"({100*collapse//n}%)")
    print(f"  ...and the v2>=1 runners miss it too -> WITNESS   : {witness} "
          f"({100*witness//n}%)")
    print()

if __name__ == "__main__":
    part_A(); part_B(int(sys.argv[1]) if len(sys.argv) > 1 else 18)
