#!/usr/bin/env python3
"""COLLAPSE + QUARTER DICHOTOMY + INTERVAL DEFICIENCY, composed.  Exact Fraction, no float.

On the collapse window W the odd runners leave a fixed odd residue v0 free (block beta0),
so by the quarter dichotomy the only possible blockers are the v2>=1 runners, and each
blocks v0 on a set whose components have length 1/(4e) at period 1/e:

   v2>=3, e:  fires on ||e t|| < 1/8                      -> length 1/(4e), period 1/e
   v2=2,  e:  fires on odds on ||e t + 1/2|| < 1/8        -> length 1/(4e), period 1/e
   v2=1,  e:  aligned on { t : block_e(t) = beta0 }       -> length 1/(4e), period 1/e

Identical shape.  So the interval-deficiency lemma applies verbatim to W:

   sum over v2>=1 runners of (floor(|W| e) + 1)/(4 e)  <  |W|   =>  FOUR witnesses.

Closed form, no search.  Composes three proved results and can fail, so it is not forced.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys

LVL = F(1, 8)
def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)
def blocked(e, t):
    return {j for j in range(8) if nrm(F(e) * (t + F(j, 8))) < LVL}
def v2(e):
    k = 0
    while e % 2 == 0: e //= 2; k += 1
    return k
ODD = (1, 3, 5, 7)

def collapse_windows(T):
    """intervals on which the odd runners' configuration is constant, near 0."""
    odd = sorted([e for e in T if e % 2], reverse=True)
    if not odd: return []
    e1 = odd[0]
    cs = sorted({F(1, 4*e) for e in odd if F(1, 4*e) < F(1, 2*e1)} | {F(0), F(1, 2*e1)})
    return [(cs[i], cs[i+1]) for i in range(len(cs)-1) if cs[i] < cs[i+1]]

def criterion(T):
    odd = [e for e in T if e % 2]
    obst = [e for e in T if v2(e) >= 1]
    for lo, hi in collapse_windows(T):
        W = hi - lo
        t = (lo + hi) / 2
        free = [v for v in ODD if not any(v in blocked(e, t) for e in odd)]
        if not free: continue
        budget = sum(F(int(W * e) + 1, 4 * e) for e in obst)
        if budget >= W: continue
        # the deficiency lemma guarantees a t in W with no obstacle; find it exactly
        cuts = []
        for e in obst:
            for k in range(int(lo * e) - 1, int(hi * e) + 2):
                cuts.append((F(k, e) - LVL / e, F(k, e) + LVL / e))
                cuts.append((F(k, e) + F(3, 8) / e, F(k, e) + F(5, 8) / e))
                for m in range(4):
                    cuts.append((F(k, e) + F(m, 4) / e, F(k, e) + F(m + 1, 4) / e))
        cuts.sort(); cur = lo; got = None
        for a, b in cuts:
            if a > cur: got = (cur + min(a, hi)) / 2; break
            cur = max(cur, b)
            if cur >= hi: break
        if got is None and cur < hi: got = (cur + hi) / 2
        if got is None: continue
        ws = []
        for k in range(4):
            f = [u for u in range(8) if not any(u in blocked(e, got + F(k, 4)) for e in T)]
            if f: ws.append(got + F(k, 4) + F(f[0], 8))
        if ws: return (W, budget, ws)
    return None

def run(box=18, cap=600):
    tuples = [T for T in combinations(range(1, box+1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//cap)]
    fires = ok = 0; fails = 0
    for T in tuples:
        r = criterion(list(T))
        if r is None: fails += 1; continue
        fires += 1
        W, b, ws = r
        if all(all(nrm(F(e) * w) >= LVL for e in T) for w in ws): ok += 1
        else: print(f"   FALSIFIED {T} ws={ws[:1]}")
    n = len(tuples)
    print(f"CLOSED-FORM criterion over {n} Case-2 tuples from [1..{box}]")
    print(f"  fires (no search -- an inequality) : {fires}  ({100*fires//n}%)")
    print(f"  every witness verified exactly     : {ok}   "
          f"{'ALL OK' if ok == fires else 'FAILURES'}")
    print(f"  CONTROL -- fails on                : {fails}  ({100*fails//n}%)  not forced")

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 18)
