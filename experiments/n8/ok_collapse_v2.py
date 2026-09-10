#!/usr/bin/env python3
"""COLLAPSE v2: the odd-runner collapse joined to the block lemma.  Exact Fraction.

v1 found the near-0 window where the ODD runners leave an odd residue free, then tested
ONE midpoint of each cell cut by the odd speeds.  Inside such a window the v2>=1 runners
move a lot, and the block lemma says exactly how:

    v2 = 1 : covers one WHOLE block; it is an ODD block iff ||2et|| > 1/4
    v2 = 2 : covers all four odd residues iff ||e t + 1/2|| < 1/8, else none
    v2 >= 3: covers everything iff ||e t|| < 1/8, else nothing

Every blocked set is constant on the cells cut by ALL breakpoints, which are the rationals
m/(8e).  So subdividing the collapse window by those and testing each cell is EXACT and
COMPLETE on that window -- no sampling.  That is the whole change.
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

def collapse_windows(T):
    """the near-0 region t < 1/(2 e^(1)), cut by the odd speeds' first jumps 1/(4e)."""
    odd = sorted([e for e in T if e % 2], reverse=True)
    if not odd: return []
    e1 = odd[0]
    cuts = sorted({F(1, 4 * e) for e in odd if F(1, 4 * e) < F(1, 2 * e1)}
                  | {F(0), F(1, 2 * e1)})
    return [(cuts[i], cuts[i + 1]) for i in range(len(cuts) - 1) if cuts[i] < cuts[i + 1]]

def collapse(T, refine):
    """refine=False reproduces v1 (one midpoint per window);
       refine=True subdivides each window by ALL breakpoints m/(8e) -- exact and complete."""
    for lo, hi in collapse_windows(T):
        if not refine:
            pts = [(lo + hi) / 2]
        else:
            cuts = {lo, hi}
            for e in T:
                a, b = int(lo * 8 * e), int(hi * 8 * e) + 2
                for m in range(a, b):
                    c = F(m, 8 * e)
                    if lo < c < hi: cuts.add(c)
            cs = sorted(cuts)
            pts = [(cs[i] + cs[i + 1]) / 2 for i in range(len(cs) - 1)]
        for t in pts:
            hit = set()
            for e in T: hit |= blocked(e, t)
            if len(hit) < 8:
                # the WITNESS is t + j/8 for an unblocked j, NOT the base point t.
                j = min(set(range(8)) - hit)
                return t + F(j, 8)
    return None

def run(box=18, cap=500):
    tuples = [T for T in combinations(range(1, box + 1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    step = max(1, len(tuples) // cap); tuples = tuples[::step]
    hi4 = [T for T in tuples if sum(1 for e in T if e % 2) >= 4]
    for name, pop in (("a >= 4", hi4), ("all Case 2", tuples)):
        v1 = v2 = ok = 0
        for T in pop:
            if collapse(list(T), False) is not None: v1 += 1
            w = collapse(list(T), True)
            if w is not None:
                v2 += 1
                if all(nrm(F(e) * w) >= LVL for e in T): ok += 1
                else: print(f"    FALSIFIED {T} w={w}")
        n = len(pop)
        print(f"{name}: {n} tuples")
        print(f"   v1  (one midpoint per window)          : {v1:>4}  ({100*v1//n}%)")
        print(f"   v2  (window subdivided, exact+complete): {v2:>4}  ({100*v2//n}%)")
        print(f"   witnesses verified exactly against all 7: {ok:>4}"
              f"   {'ALL OK' if ok == v2 else 'FAILURES'}")
        print(f"   gain: +{v2-v1} tuples\n")
    return tuples

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 18)

# ---------------------------------------------------------------- widen the window
def collapse_wide(T, upto=F(1, 2)):
    """same, but search t up to `upto` instead of only the near-0 region 1/(2 e^(1)).
    Still exact and complete: all breakpoints are m/(8e)."""
    cuts = {F(0), upto}
    for e in T:
        for m in range(0, int(upto * 8 * e) + 2):
            c = F(m, 8 * e)
            if 0 < c < upto: cuts.add(c)
    cs = sorted(cuts)
    for i in range(len(cs) - 1):
        t = (cs[i] + cs[i + 1]) / 2
        hit = set()
        for e in T: hit |= blocked(e, t)
        if len(hit) < 8:
            j = min(set(range(8)) - hit)
            return t + F(j, 8)
    return None

def survey(box=20, cap=1500):
    tuples = [T for T in combinations(range(1, box + 1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    step = max(1, len(tuples) // cap); tuples = tuples[::step]
    near = wide = okn = okw = 0
    resid = []
    for T in tuples:
        w = collapse(list(T), True)
        if w is not None:
            near += 1
            if all(nrm(F(e) * w) >= LVL for e in T): okn += 1
        else:
            resid.append(T)
        w2 = collapse_wide(list(T), F(1, 8))
        if w2 is not None:
            wide += 1
            if all(nrm(F(e) * w2) >= LVL for e in T): okw += 1
    n = len(tuples)
    print(f"\nCase-2 sample from [1..{box}]: {n} tuples")
    print(f"  collapse v2, near-0 window t < 1/(2 e1) : {near:>5} ({100*near//n}%)"
          f"   verified {okn}")
    print(f"  same, widened to t < 1/8                : {wide:>5} ({100*wide//n}%)"
          f"   verified {okw}")
    print(f"  residue after the near-0 window          : {len(resid)}")
    print(f"  residual tuples: {resid[:8]}")
    still = [T for T in resid if collapse_wide(list(T), F(1, 8)) is None]
    print(f"  of those, still unsettled after widening : {len(still)}  {still[:8]}")

survey()
