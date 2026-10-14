#!/usr/bin/env python3
"""THE  sum(alpha) < 1  CRITERION, with |O| >= 2.  Exact Fraction, no float.

|G(E)| >= |G(H)| (1 - sum_{x in O} alpha_x),  alpha_x = |A_x n G(H)|/|G(H)|,  O = E \\ H.

  sum alpha_x < 1  =>  a witness.                                    [PROVED]

NON-CIRCULAR for |O| >= 2: the converse fails (overlaps can save a tuple whose alphas sum
above 1), so the criterion can fail while a witness exists -- and it does.  For |O| = 1 it
IS circular (alpha_x < 1 restates |G| > 0), so |O| = 1 is EXCLUDED throughout.

Why it should work: psi has mean zero (3/512 + 0 - 3/512 = 0), so S_x is a mean-zero
periodic function and about half of all speeds have S_x < 0, i.e. alpha_x < 1/4 -- better
than generic.  Generic sum over |O|=2 is 1/2, leaving room to 1.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys

def ivs(E):
    out = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8*k-1, 8*e), F(0)), min(F(8*k+1, 8*e), F(1))
            if lo < hi: out.append((lo, hi))
    return out
def merge(iv):
    iv = sorted(iv); m = []
    for lo, hi in iv:
        if m and lo <= m[-1][1]: m[-1][1] = max(m[-1][1], hi)
        else: m.append([lo, hi])
    return m
def comp(m):
    g, cur = [], F(0)
    for lo, hi in m:
        if cur < lo: g.append((cur, lo))
        cur = max(cur, hi)
    if cur < 1: g.append((cur, F(1)))
    return g
def meas(iv): return sum(hi - lo for lo, hi in iv)
def inter(a, b):
    out, i, j = [], 0, 0
    while i < len(a) and j < len(b):
        lo, hi = max(a[i][0], b[j][0]), min(a[i][1], b[j][1])
        if lo < hi: out.append((lo, hi))
        if a[i][1] < b[j][1]: i += 1
        else: j += 1
    return out

def criterion(T):
    """smallest sum(alpha) over subsets O with |O| in {2,3,4}; returns (sum, O) or None."""
    best = None
    n = len(T)
    for r in (2, 3, 4):
        for O in combinations(range(n), r):
            H = [T[i] for i in range(n) if i not in O]
            g = comp(merge(ivs(H))); mg = meas(g)
            if mg == 0: continue
            s = sum(meas(inter(merge(ivs([T[i]])), g)) / mg for i in O)
            if best is None or s < best[0]: best = (s, [T[i] for i in O])
            if s < 1: return (s, [T[i] for i in O], True)
    return (best[0], best[1], False) if best else None

def run(box=18, cap=400):
    tuples = [T for T in combinations(range(1, box+1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//cap)]
    fires = 0; fails = []
    from collections import Counter
    bya = Counter(); fa = Counter()
    for T in tuples:
        a = sum(1 for e in T if e % 2); bya[a] += 1
        r = criterion(list(T))
        if r and r[2]: fires += 1; fa[a] += 1
        else: fails.append((T, r[0] if r else None))
    n = len(tuples)
    print(f"sum(alpha) < 1  over {n} Case-2 tuples from [1..{box}]   (|O| >= 2 only)")
    print(f"  fires : {fires}  ({100*fires//n}%)     fails : {len(fails)}  (not forced)")
    print(f"  by a = #odd speeds:")
    for a in sorted(bya): print(f"    a={a}: {fa[a]:>4} / {bya[a]:>4}")
    if fails:
        fails.sort(key=lambda x: x[1])
        print(f"  closest misses (tuple, min sum alpha):")
        for T, s in fails[:5]: print(f"    {T}  {float(s):.4f}")
    print(f"\n  the extremum:")
    r = criterion([2,6,7,8,10,13,14])
    print(f"    (2,6,7,8,10,13,14)  min sum alpha = {r[0]} = {float(r[0]):.6f}"
          f"  via O={r[1]}   fires={r[2]}")

if __name__ == "__main__":
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 18)

# ---------------------------------------------------------------- soundness control
def control():
    """DECISIVE: the three tight instances have |G| = 0.  sum(alpha) < 1 would imply
    |G| >= |G_H|(1 - sum) > 0.  So a SOUND criterion must FAIL on all three.  If it fires
    on any, the implementation is wrong.  Also: how much slack is there at the extremum?"""
    print("\nSOUNDNESS CONTROL -- the three tight instances (|G| = 0 exactly)")
    for T, lab in (([1,2,3,4,5,6,7], "T1 = the AP"),
                   ([1,2,3,4,5,7,12], "T2"),
                   ([1,4,5,6,7,11,13], "T3")):
        g = meas(comp(merge(ivs(T))))
        best = None; n = len(T)
        for r in (2, 3, 4):
            for O in combinations(range(n), r):
                H = [T[i] for i in range(n) if i not in O]
                gg = comp(merge(ivs(H))); mg = meas(gg)
                if mg == 0: continue
                s = sum(meas(inter(merge(ivs([T[i]])), gg)) / mg for i in O)
                if best is None or s < best[0]: best = (s, [T[i] for i in O])
        fired = best[0] < 1
        print(f"  {lab:<12} {str(tuple(T)):<22} |G|={g}   min sum alpha = "
              f"{str(best[0]):>12} = {float(best[0]):.6f}  fires={fired}   "
              f"{'UNSOUND!' if fired else 'correctly fails'}")

    print("\nSLACK at the extremum and its neighbours (true MINIMUM over all O, |O|>=2)")
    for T in ([2,6,7,8,10,13,14], [1,3,4,5,7,11,24], [1,2,3,4,5,7,24], [1,4,5,6,7,11,16]):
        n = len(T); best = None
        for r in (2, 3, 4):
            for O in combinations(range(n), r):
                H = [T[i] for i in range(n) if i not in O]
                gg = comp(merge(ivs(H))); mg = meas(gg)
                if mg == 0: continue
                s = sum(meas(inter(merge(ivs([T[i]])), gg)) / mg for i in O)
                if best is None or s < best[0]: best = (s, [T[i] for i in O])
        print(f"  {str(tuple(T)):<26} min sum alpha = {str(best[0]):>14} = "
              f"{float(best[0]):.6f}   via O={best[1]}   margin {float(1-best[0]):.6f}")

control()

# ---------------------------------------------------------------- is it LOSSY?
def lossy_test(box=16, cap=500):
    """If min_O sum(alpha) < 1 were EQUIVALENT to |G| > 0 it would be a restatement, not a
    criterion.  Test on CASE-1 tuples (no multiple of 8) that are NOT tight: any with
    |G| > 0 but min sum alpha >= 1 proves the criterion is strictly stronger, i.e. lossy
    and non-equivalent."""
    print("\nLOSSY TEST -- Case-1 tuples (no multiple of 8), |G| > 0")
    tuples = [T for T in combinations(range(1, box+1), 7)
              if reduce(gcd, T) == 1 and not any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//cap)]
    lossy = []; fired = 0; zero = 0
    for T in tuples:
        g = meas(comp(merge(ivs(list(T)))))
        if g == 0: zero += 1; continue
        n = len(T); best = None
        for r in (2, 3):
            for O in combinations(range(n), r):
                H = [T[i] for i in range(n) if i not in O]
                gg = comp(merge(ivs(H))); mg = meas(gg)
                if mg == 0: continue
                s = sum(meas(inter(merge(ivs([T[i]])), gg)) / mg for i in O)
                if best is None or s < best: best = s
        if best is not None and best < 1: fired += 1
        else: lossy.append((T, float(g), float(best) if best else None))
    n = len(tuples) - zero
    print(f"  {n} non-tight Case-1 tuples ({zero} tight, excluded)")
    print(f"  criterion fires : {fired}   FAILS while |G| > 0 : {len(lossy)}")
    if lossy:
        print(f"  -> the criterion is LOSSY, hence NOT a restatement of |G| > 0.")
        for T, g, b in lossy[:5]:
            print(f"     {T}  |G|={g:.6f}  min sum alpha={b:.6f}")
    else:
        print(f"  -> no loss observed here; equivalence NOT ruled out on this frame.")

def bigger_box(box=22, cap=250):
    print(f"\nBIGGER BOX -- Case 2 from [1..{box}]")
    tuples = [T for T in combinations(range(1, box+1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    tuples = tuples[::max(1, len(tuples)//cap)]
    fires = 0; worst = None
    for T in tuples:
        n = len(T); best = None
        for r in (2, 3):
            for O in combinations(range(n), r):
                H = [T[i] for i in range(n) if i not in O]
                gg = comp(merge(ivs(H))); mg = meas(gg)
                if mg == 0: continue
                s = sum(meas(inter(merge(ivs([T[i]])), gg)) / mg for i in O)
                if best is None or s < best: best = s
        if best is not None and best < 1: fires += 1
        if best is not None and (worst is None or best > worst[0]): worst = (best, T)
    print(f"  {len(tuples)} tuples;  fires {fires}  ({100*fires//len(tuples)}%)")
    print(f"  largest min-sum-alpha (smallest margin): {float(worst[0]):.6f} at {worst[1]}")

lossy_test(); bigger_box()
