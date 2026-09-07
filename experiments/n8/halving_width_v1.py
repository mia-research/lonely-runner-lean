#!/usr/bin/env python3
"""Theorem P' -- a WIDTH invariant replacing Theorem P's counting invariant.

HALVING_AND_TIGHT_WITNESS_v1.md sec 5.2: Theorem P's "loss is the worst-case grid count
floor(g_u/4)+1 ... four such can tile Z/g exactly, so x <= 3 is close to the limit of THIS
counting.  A different invariant is needed, not a sharper count."

Theorem P's skeleton is kept: for D subset of T, g = gcd(D), X = T\D, U_D is invariant
under t -> t + 1/g, so  S^1 = U_D  union  intersection_j (U_X + j/g).  P kills the
intersection by COUNTING shifts.  P' kills it by WIDTH:

  TOP_GAP_v1.md Lemma 2, from LRC(x+1) which this project owns machine-verified for
  x+1 <= 7: for x distinct positive integers with maximum Mx, there is t0 with
  min ||u t0|| >= 1/(x+1); perturbing by |d| < (1/(x+1) - 1/8)/Mx keeps every
  ||u t|| > 1/8.  So the level-1/8 lonely set of X contains an interval of length

      L(x, Mx) = 2 * (1/(x+1) - 1/8) / Mx = (7-x) / (4 (x+1) Mx).

  If 1/g < L then EVERY coset t + (1/g)Z meets that interval, so some shift j has
  t - j/g lonely for X, so the intersection is empty, so U_D = S^1; substituting
  t = s/g gives M(D/g) <= 1/8, contradicting LRC(8-x) >= 1/(8-x) > 1/8.

  THEOREM P'.  If  g * (7-x) > 4 (x+1) max(X)  then  M(T) > 1/8.

FRAME, fixed before running: all 7-subsets of {1,...,B} with gcd = 1 in the RESIDUAL
class R (holding a multiple of 5, of 6, of 7 and of 8) -- the class HALVING sec 1 proves
LRC(8) equivalent to.  B = 24 (and 28 if time allows).  D ranges over all 127 non-empty
proper subsets.  Exact integer/rational arithmetic only.
"""
import sys
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations

def Mval(T):
    """max_t min_v ||v t|| exactly: peaks (2k+1)/(2v) and crossings k/(v_i +- v_j)."""
    C = set()
    for v in T:
        for k in range(2 * v):
            C.add(F(2 * k + 1, 2 * v))
    for a, b in combinations(T, 2):
        for s in (a + b, abs(a - b)):
            if s:
                for k in range(s + 1):
                    C.add(F(k, s))
    best = F(0)
    for t in C:
        if not (0 <= t <= 1): continue
        m = min(min(x := (v * t) % 1, 1 - x) for v in T)
        if m > best: best = m
    return best

def theoremP(T):
    """Original: exists D (via m) with sum_u h_u(floor(g_u/4)+1) < g."""
    for m in range(2, max(T) + 1):
        D = [v for v in T if v % m == 0]
        X = [v for v in T if v % m]
        if not D or not (1 <= len(X) <= 6): continue
        g = reduce(gcd, D)
        tot = 0
        for u in X:
            h = gcd(u, g); tot += h * ((g // h) // 4 + 1)
        if tot < g: return True
    return False

def theoremPprime(T):
    """New: exists D subset T with g(7-x) > 4(x+1)max(X)."""
    n = len(T)
    for r in range(1, n):
        for D in combinations(T, r):
            X = [v for v in T if v not in D]
            x = len(X)
            if not (1 <= x <= 6): continue
            g = reduce(gcd, D)
            if g * (7 - x) > 4 * (x + 1) * max(X): return True
    return False

def residual(T):
    return all(any(v % q == 0 for v in T) for q in (5, 6, 7, 8))

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    TIGHT = [(1,2,3,4,5,6,7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13)]
    print("CONTROL -- the three tight instances (M = 1/8) must FAIL both hypotheses,")
    print("           or the theorem is false.")
    for T in TIGHT:
        print(f"   {list(T)}  M={Mval(T)}  P={theoremP(T)}  P'={theoremPprime(T)}"
              + ("   <-- VIOLATION" if theoremP(T) or theoremPprime(T) else "   ok"))
    print()
    tot = nP = nPp = nBoth = nEither = 0
    viol = []
    for T in combinations(range(1, B + 1), 7):
        if reduce(gcd, T) != 1 or not residual(T): continue
        tot += 1
        p, pp = theoremP(T), theoremPprime(T)
        nP += p; nPp += pp; nBoth += (p and pp); nEither += (p or pp)
        if pp and Mval(T) <= F(1, 8): viol.append(T)
    print(f"FRAME: residual 7-subsets of [1,{B}] with gcd 1 : {tot}")
    print(f"   settled by Theorem P  (counting) : {nP:>7}  ({100.0*nP/tot:.2f}%)")
    print(f"   settled by Theorem P' (width)    : {nPp:>7}  ({100.0*nPp/tot:.2f}%)")
    print(f"   both                             : {nBoth:>7}")
    print(f"   EITHER                           : {nEither:>7}  ({100.0*nEither/tot:.2f}%)")
    print(f"   P' adds over P alone             : {nEither-nP:>7}")
    print(f"   forward check, sets where P' fires but M <= 1/8 (must be 0): {len(viol)}")
    if viol: print("   VIOLATIONS:", viol[:5])
