"""
n=8, DROPPED-UNIT leaf, representative speeds.

R_non = {1..7} minus an absent PAIR A, where A contains at least one unit
(units of Z/8 = {1,3,5,7}).  There are C(7,2)-C(3,2) = 21-3 = 18 such pairs.
E_non = R_non (representative speeds), so |E_non| = 5 and |E_div| = 2.

Computes, for each absent pair, the exact SAFE set
    S(A) = { x in [0,1) : union_{e in E_non} bad(e, floor(e x))  !=  Z/8 }
by exact rational cell decomposition, with BOUNDARY-EXACT floors:
  (A) completeness -- no breakpoint strictly inside any cell (exact rational test);
  (B) entry value floor(e*a) equals exit value floor(e*b) - [e*b integer];
      and the covered set computed at entry equals the one computed at exit.
No midpoint is ever evaluated.  No floating point in any decision.

Also reports, for every maximal window of S, the FULL list of residues that remain
uncovered at each constituent cell (discipline requirement (ii)).
"""
from fractions import Fraction as F
from itertools import combinations

UNITS = {1,3,5,7}
FULL  = frozenset(range(8))

def bad(e,t):
    return frozenset(r for r in range(8) if (e*r+t) % 8 in (0,7))

def cells(speeds):
    pts = {F(0), F(1)}
    for e in speeds:
        for j in range(1, e+1):
            q = F(j, e)
            if 0 < q < 1: pts.add(q)
    p = sorted(pts)
    return list(zip(p, p[1:]))

def floor_entry(e,a):
    v = e*a; return v.numerator // v.denominator
def floor_exit(e,b):
    v = e*b; f = v.numerator // v.denominator
    return f-1 if v.denominator == 1 else f

def analyse(Enon):
    C = cells(Enon)
    interior = 0; mismatch = 0; entryexit_setdiff = 0
    meas = F(0); safecells = []
    for a,b in C:
        for e in Enon:
            lo = e*a
            k0 = lo.numerator // lo.denominator + 1
            if a < F(k0,e) < b: interior += 1
            if floor_entry(e,a) != floor_exit(e,b): mismatch += 1
        cov_in  = set(); cov_out = set()
        for e in Enon:
            cov_in  |= bad(e, floor_entry(e,a))
            cov_out |= bad(e, floor_exit(e,b))
        if cov_in != cov_out: entryexit_setdiff += 1
        if cov_in != FULL:
            meas += b - a
            safecells.append((a,b,tuple(sorted(FULL-cov_in))))
    # maximal windows = maximal runs of contiguous safe cells (any uncovered set)
    windows = []
    for a,b,u in safecells:
        if windows and windows[-1][1] == a:
            windows[-1][1] = b; windows[-1][2].append((a,b,u))
        else:
            windows.append([a,b,[(a,b,u)]])
    return dict(ncells=len(C), interior=interior, mismatch=mismatch,
                setdiff=entryexit_setdiff, meas=meas, windows=windows)

pairs = [A for A in combinations(range(1,8),2) if set(A) & UNITS]
assert len(pairs) == 18

rows = []
print(f"{len(pairs)} absent pairs with at least one unit\n")
tot_int = tot_mis = tot_sd = 0
for A in pairs:
    Enon = sorted(set(range(1,8)) - set(A))
    R = analyse(Enon)
    tot_int += R['interior']; tot_mis += R['mismatch']; tot_sd += R['setdiff']
    widest = max((w[1]-w[0] for w in R['windows']), default=F(0))
    rows.append((A, Enon, R, widest))
    print(f"absent {A}  E_non={Enon}")
    print(f"   |S| = {R['meas']}  ({float(R['meas']):.5f})   >1/2 ? {R['meas']>F(1,2)}"
          f"   #windows={len(R['windows'])}   widest={widest} ({float(widest):.5f})")
    for lo,hi,parts in R['windows']:
        us = sorted({u for _,_,u in parts})
        print(f"      W=[{lo},{hi}) len {hi-lo}  cells {len(parts)}  uncovered sets {us}")
    print(f"   boundary audit: cells={R['ncells']} interior-breakpoints={R['interior']}"
          f" entry/exit-mismatch={R['mismatch']} entry-vs-exit cover diff={R['setdiff']}")
    print()

print("="*70)
print(f"TOTAL boundary audit over all 18 pairs: interior breakpoints={tot_int}, "
      f"entry/exit floor mismatches={tot_mis}, entry-vs-exit covered-set diffs={tot_sd}")
print()
print("Pairs with |S| <= 1/2 (union bound insufficient):")
for A,Enon,R,widest in rows:
    if R['meas'] <= F(1,2):
        print(f"   absent {A}  E_non={Enon}  |S|={R['meas']}  widest window={widest}"
              f"  -> needs |W| >= 1/m i.e. m >= {F(1,1)/widest if widest else None}")
