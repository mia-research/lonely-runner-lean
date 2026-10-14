#!/usr/bin/env python3
"""THE QUARTER-SHIFT CYCLE.  Exact Fraction, no float.

Under t -> t + 1/4:  an odd runner has q_e -> q_e + chi_1(rho_e)  (a UNIT step in Z/4);
a v2=1 runner e=2w has 2e(t+1/4) = 2et + w, so its odd/even side is INVARIANT while its
block shifts by 2 mod 4 -- it ALTERNATES between the two blocks of its parity; a v2>=2
runner has e/4 in Z, so it is completely INVARIANT (fires at all four times or none).

Claims to test, exactly:
  C1  over the four times t + k/4, each odd runner blocks each odd residue exactly once;
  C2  in a collapse configuration the collision PERSISTS at all four times, and the freed
      odd residue cycles through all four, alternating block A={1,5} / B={3,7};
  C3  each v2=1 runner blocks the freed residue at ALL four times or at NONE (dichotomy).

If C2 and C3 hold then: no v2>=2 runner firing + no v2=1 runner aligned  =>  FOUR witnesses.
That is a structural certificate, not a window search -- it can fail, so it is not forced.
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
BLK = lambda j: j % 4          # 1 -> A={1,5}, 3 -> B={3,7}

def windows(T):
    odd = sorted([e for e in T if e % 2], reverse=True)
    if not odd: return []
    e1 = odd[0]
    cs = sorted({F(1, 4*e) for e in odd if F(1, 4*e) < F(1, 2*e1)} | {F(0), F(1, 2*e1)})
    return [((cs[i]+cs[i+1])/2) for i in range(len(cs)-1) if cs[i] < cs[i+1]]

def audit(box=16, cap=400):
    tuples = [T for T in combinations(range(1, box+1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//cap)]
    c1 = c2 = c3 = n1 = n2 = n3 = 0
    for T in tuples:
        odd = [e for e in T if e % 2]
        for t in windows(list(T)):
            # C1
            for e in odd:
                got = [next(iter({j for j in blocked(e, t + F(k,4)) if j % 2})) for k in range(4)]
                n1 += 1
                if sorted(got) == list(ODD): c1 += 1
            # collapse configuration?  odd runners leave an odd residue free at k=0
            free0 = [v for v in ODD if not any(v in blocked(e, t) for e in odd)]
            if len(free0) != 1: continue
            frees = []
            for k in range(4):
                f = [v for v in ODD if not any(v in blocked(e, t + F(k,4)) for e in odd)]
                frees.append(f)
            n2 += 1
            if all(len(f) == 1 for f in frees) and sorted(f[0] for f in frees) == list(ODD):
                c2 += 1
                alt = [BLK(f[0]) for f in frees]
                # C3: each v2=1 runner blocks the freed residue at all four times or none
                for e in T:
                    if v2(e) != 1: continue
                    hits = sum(1 for k in range(4)
                               if frees[k][0] in blocked(e, t + F(k,4)))
                    n3 += 1
                    if hits in (0, 4): c3 += 1
    print(f"C1  odd runner blocks each odd residue exactly once over the 4 times : "
          f"{c1}/{n1}  {'HOLDS' if c1==n1 else 'FAILS'}")
    print(f"C2  freed residue cycles through all four odds                       : "
          f"{c2}/{n2}  {'HOLDS' if c2==n2 else 'FAILS'}")
    print(f"C3  each v2=1 runner blocks it at ALL four times or NONE             : "
          f"{c3}/{n3}  {'HOLDS' if c3==n3 else 'FAILS'}")

if __name__ == "__main__":
    audit(int(sys.argv[1]) if len(sys.argv) > 1 else 16)

# ---------------------------------------------------------------- the certificate
def certificate(T):
    """At a collapse configuration, the freed residue's only possible blockers are the
    v2>=1 runners, and the same set blocks it at ALL FOUR quarter-shifts.  So:

        no v2>=2 runner fires  AND  no v2=1 runner shares the freed residue's block
        =>  FOUR witnesses, certified at a single t.

    Returns (t, freed, witnesses) or None.  Structural, single-point, and it CAN fail."""
    odd = [e for e in T if e % 2]
    for t in windows(T):
        free = [v for v in ODD if not any(v in blocked(e, t) for e in odd)]
        if len(free) != 1: continue
        v = free[0]
        if any(v in blocked(e, t) for e in T if v2(e) >= 1):   # a blocker at k=0
            continue
        ws = []
        for k in range(4):
            f = [u for u in ODD if not any(u in blocked(e, t + F(k,4)) for e in T)]
            if not f: return None                              # dichotomy would be violated
            ws.append(t + F(k,4) + F(f[0], 8))
        return (t, v, ws)
    return None

def measure(box=18, cap=600):
    tuples = [T for T in combinations(range(1, box+1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//cap)]
    fires = ok = 0
    fails = []
    for T in tuples:
        r = certificate(list(T))
        if r is None:
            fails.append(T); continue
        fires += 1
        t, v, ws = r
        if all(all(nrm(F(e)*w) >= LVL for e in T) for w in ws): ok += 1
        else: print(f"   FALSIFIED {T}")
    n = len(tuples)
    print(f"\nCERTIFICATE over {n} Case-2 tuples from [1..{box}]")
    print(f"  fires (single-point, structural)     : {fires}  ({100*fires//n}%)")
    print(f"  all FOUR witnesses verified exactly  : {ok}   "
          f"{'ALL OK' if ok == fires else 'FAILURES'}")
    print(f"  CONTROL -- it fails on               : {len(fails)}  "
          f"({100*len(fails)//n}%)  so it is NOT forced")
    print(f"  examples of failure: {fails[:5]}")
    # what causes failure?
    from collections import Counter
    why = Counter()
    for T in fails:
        odd = [e for e in T if e % 2]
        found = False
        for t in windows(list(T)):
            fr = [v for v in ODD if not any(v in blocked(e, t) for e in odd)]
            if len(fr) == 1:
                found = True
                if any(fr[0] in blocked(e, t) for e in T if v2(e) >= 2): why["v2>=2 fires"] += 1
                elif any(fr[0] in blocked(e, t) for e in T if v2(e) == 1): why["v2=1 aligned"] += 1
                break
        if not found: why["no collapse window"] += 1
    print(f"  cause of failure: {dict(why)}")

measure()
