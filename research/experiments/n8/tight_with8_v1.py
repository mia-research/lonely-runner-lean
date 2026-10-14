#!/usr/bin/env python3
"""OPEN QUESTION: is any 7-set carrying a multiple of 8 TIGHT at n=8?
'Tight' = M(T) = 1/8 exactly = the level-1/8 lonely set has NO positive-length component
but is non-empty.  HALVING_AND_TIGHT_WITNESS_v1 sec 4 checked speeds <= 44 for the residual
class using a FLOAT first stage; this run is exact throughout, no float anywhere.

Necessary conditions applied first, both exact and both proved:
  gcd(T) = 1                                  (normalisation)
  every q in {2,...,7} divides some speed     (else M >= 1/q > 1/8, so not tight)
Sharded into independent processes -- no multiprocessing.Pool, which died silently earlier.
Usage: tight_with8_v1.py <bound> <shard> <nshards>
"""
import sys, io, contextlib
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
sys.path.insert(0, "experiments/n8")
with contextlib.redirect_stdout(io.StringIO()):
    from exact_phi_n_ap_v1 import lonely_set
n = 8

def tight(T):
    """Exact: M(T) = 1/8  iff  no positive-length lonely component and some lonely point."""
    pts, ivs = lonely_set(list(T), n)
    return (not ivs) and bool(pts), pts

if __name__ == "__main__":
    B, shard, ns = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seen = tested = 0; hits = []
    for T in combinations(range(1, B + 1), 7):
        if not any(v % 8 == 0 for v in T): continue
        if reduce(gcd, T) != 1: continue
        if not all(any(v % q == 0 for v in T) for q in (2,3,4,5,6,7)): continue
        seen += 1
        if seen % ns != shard: continue
        tested += 1
        ok, pts = tight(T)
        if ok: hits.append((list(T), [str(x) for x in pts]))
    print(f"shard {shard}/{ns}  bound {B}: candidates-with-multiple-of-8 {seen}, "
          f"tested {tested}, TIGHT {len(hits)}")
    for h in hits: print("   TIGHT:", h)
