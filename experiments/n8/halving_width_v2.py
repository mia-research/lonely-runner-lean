#!/usr/bin/env python3
"""Theorem P'' -- the width invariant with the lossy constant REMOVED.

v1 derived the width from LRC(x+1) + a perturbation, giving L >= (7-x)/(4(x+1)max X).
Measured: that settles 79 of 12673 residual sets at B=20, ALL of them already settled by
Theorem P.  Net gain zero.  The loss is the constant.

P'' drops the bound and uses the EXACT widest lonely interval, computed by the Boundary
Set Method over Fraction:

    lambda(X) := the largest connected component of  { t : ||u t|| >= 1/8  for all u in X }.

  THEOREM P''.  D subset of T non-empty, g = gcd(D), X = T\\D, 1 <= |X| <= 6.
                If  1/g < lambda(X)  then  M(T) > 1/8.

  Proof identical to P and P': U_D is invariant under t -> t + 1/g, so
  S^1 = U_D union intersection_j (U_X + j/g).  If 1/g < lambda(X) then every coset
  t + (1/g)Z meets the widest lonely component of X, so some shift j has t - j/g outside
  U_X, so the intersection is empty, so U_D = S^1; t = s/g gives M(D/g) <= 1/8,
  contradicting LRC(8-x) >= 1/(8-x) > 1/8.  LRC(3..7) are owned machine-verified.

P'' implies P' (the bound is a lower bound on lambda) so it can only gain.
FRAME as v1: residual 7-subsets of [1,B], gcd 1, D over all 127 non-empty proper subsets.
Exact rationals throughout; lambda memoised by X.
"""
import sys, io, contextlib
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
sys.path.insert(0, "experiments/n8")
with contextlib.redirect_stdout(io.StringIO()):
    from exact_phi_n_ap_v1 import lonely_set
from halving_width_v1 import Mval, theoremP, residual

_lam = {}
def lam(X):
    """Exact widest lonely component of X at level 1/8 (0 if none)."""
    k = tuple(X)
    if k in _lam: return _lam[k]
    pts, ivs = lonely_set(list(X), 8)
    out = []
    for a, c in sorted(ivs):
        if out and a <= out[-1][1]: out[-1][1] = max(out[-1][1], c)
        else: out.append([a, c])
    v = max((c - a for a, c in out), default=F(0))
    _lam[k] = v
    return v

def theoremPpp(T):
    for r in range(1, len(T)):
        for D in combinations(T, r):
            X = tuple(v for v in T if v not in D)
            if not (1 <= len(X) <= 6): continue
            g = reduce(gcd, D)
            if g and F(1, g) < lam(X): return True
    return False

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    print("CONTROL -- the three tight instances must FAIL P'' or the theorem is false.")
    for T in [(1,2,3,4,5,6,7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13)]:
        r = theoremPpp(T)
        print(f"   {list(T)}  M={Mval(T)}  P''={r}" + ("   <-- VIOLATION" if r else "   ok"))
    print()
    tot = nP = nPpp = nEither = 0; viol = []
    for T in combinations(range(1, B + 1), 7):
        if reduce(gcd, T) != 1 or not residual(T): continue
        tot += 1
        p, pp = theoremP(T), theoremPpp(T)
        nP += p; nPpp += pp; nEither += (p or pp)
        if pp and Mval(T) <= F(1, 8): viol.append(T)
    print(f"FRAME: residual 7-subsets of [1,{B}] with gcd 1 : {tot}")
    print(f"   Theorem P   (counting)      : {nP:>7}  ({100.0*nP/tot:.2f}%)")
    print(f"   Theorem P'' (exact width)   : {nPpp:>7}  ({100.0*nPpp/tot:.2f}%)")
    print(f"   EITHER                      : {nEither:>7}  ({100.0*nEither/tot:.2f}%)")
    print(f"   P'' ADDS over P alone       : {nEither-nP:>7}")
    print(f"   forward check, P'' fires but M <= 1/8 (must be 0): {len(viol)}")
    if viol: print("   VIOLATIONS:", viol[:5])
