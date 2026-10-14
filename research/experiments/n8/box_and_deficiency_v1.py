#!/usr/bin/env python3
"""(1) THE BOX CHECK and (2) THE INTERVAL-DEFICIENCY THEOREM.  Exact Fraction, no float
on any decision path (floats appear only as a REJECTION pre-filter in part 1, and every
survivor is re-decided exactly).

(1) BOX.  v33 Lemma 5.1 gives the sign range a_j in (j-1, j+1) for a completely blocking
configuration; TIGHT_INSTANCES_v1 §5 records the naive n=8 analogue failing on two tight
instances, both of which lack a multiple of 8.  The open question was whether the box
survives on the RESIDUAL class -- tuples carrying a multiple of 8.  Settled here by
enumerating the tight instances outright.
  tight  <=>  M(T) = 1/8  <=>  the CLOSED bad sets [ (8k-1)/8v, (8k+1)/8v ] cover [0,1]
  (M(T) >= 1/8 always, since LRC(8) is true).
  ladder filter: for q in 2..7, some speed divisible by q, else t = 1/q gives M > 1/8.

(2) INTERVAL DEFICIENCY.  Let H be ANY subset of T with h = |H| <= 6, L = T \\ H.
LRC(h+1) gives t0 with ||v t0|| >= 1/(h+1) for v in H.  For |d| <= eta :=
(1/(h+1) - 1/8)/max(H) every v in H still has ||v(t0+d)|| >= 1/8, so the interval J of
length l = 2*eta is good for all of H.  A speed v in L meets at most floor(l*v)+1
components of its bad set, each of length 1/(4v), so it covers at most (floor(l v)+1)/(4v)
of J.  Hence

    sum over v in L of (floor(l*v)+1)/(4*v)  <  l    ==>   T has the LR property.

|L| = 1 with H the six smallest returns TOP_GAP (v7 > 7 v6) exactly.  |L| = 2, 3 are new.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys

LEVEL = F(1, 8)
def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)

# ---------------------------------------------------------------- part 1
def closed_bad(v, lvl=LEVEL):
    """closed bad set of v at lvl, as exact intervals clipped to [0,1]."""
    out, num, den = [], lvl.numerator, lvl.denominator
    for k in range(0, v + 1):
        lo, hi = F(k, v) - lvl / v, F(k, v) + lvl / v
        lo, hi = max(lo, F(0)), min(hi, F(1))
        if lo <= hi: out.append((lo, hi))
    return out

def covers_unit(iv):
    """do the closed intervals cover [0,1] exactly?"""
    iv = sorted(iv)
    reach = F(0)
    for lo, hi in iv:
        if lo > reach: return False
        reach = max(reach, hi)
        if reach >= 1: return True
    return reach >= 1

def is_tight(T):
    """M(T) = 1/8 exactly, i.e. no t has min ||v t|| > 1/8."""
    return covers_unit([x for v in T for x in closed_bad(v)])

def float_maybe_tight(T, tol=1e-9):
    pts = []
    for v in T:
        w = 0.125 / v
        for k in range(v + 1):
            pts.append((k / v - w, k / v + w))
    pts.sort()
    reach = 0.0
    for lo, hi in pts:
        if lo > reach + tol: return False
        if hi > reach: reach = hi
    return reach >= 1.0 - tol

def part1(N=26):
    Q = range(2, 8)
    tight = []
    cand = tested = 0
    for T in combinations(range(1, N + 1), 7):
        if reduce(gcd, T) != 1: continue
        if any(all(v % q for v in T) for q in Q): continue      # witness-ladder filter
        cand += 1
        if not float_maybe_tight(T): continue
        tested += 1
        if is_tight(T): tight.append(T)
    print(f"PART 1 -- tight instances at n=8, exhaustive over speeds <= {N}")
    print(f"  candidates past gcd + witness-ladder filter : {cand}")
    print(f"  survived the float rejection, re-decided exactly : {tested}")
    print(f"  TIGHT (M(T) = 1/8) : {len(tight)}")
    with8 = [T for T in tight if any(v % 8 == 0 for v in T)]
    print(f"  of these, carrying a multiple of 8 : {len(with8)}   {with8}")
    print()
    print("  a-vector a_i = 7 e_i / e_7, and the box a_j in (j-1, j+1) for j = 2..6:")
    for T in tight:
        a = [F(7 * e, T[-1]) for e in T]
        flags = "".join("." if F(j - 1) < a[j - 1] < F(j + 1) else "X" for j in range(2, 7))
        print(f"    {str(list(T)):<26} a = {[str(x) for x in a]}")
        print(f"    {'':<26} box j=2..6 : {flags}   ({'holds' if 'X' not in flags else 'FAILS'})")
    print()
    return tight

# ---------------------------------------------------------------- part 2
def good_set(S, lvl):
    """{t in [0,1] : ||v t|| >= lvl for all v in S}, EXACT, as closed components --
    isolated points included.  The bad sets are complemented as OPEN intervals and merged
    only on STRICT overlap, so two bad intervals that merely touch leave their touch point
    in the good set.  This matters: the lonely set at level 1/(h+1) is a single point
    whenever H is a tight instance of LRC(h+1) -- {1,..,6} at 1/7 is exactly that -- and
    treating the bad sets as closed, or merging on contact, silently deletes the extremal
    case and can even manufacture a spurious 'good' point at t = 0."""
    iv = sorted((F(k, v) - lvl / v, F(k, v) + lvl / v)
                for v in S for k in range(-1, v + 2))
    merged = []
    for lo, hi in iv:
        if merged and lo < merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    good, cur = [], F(0)
    for lo, hi in merged:
        if lo > 1: break
        if cur <= lo:
            a, b = max(cur, F(0)), min(lo, F(1))
            if a <= b: good.append((a, b))
        cur = max(cur, hi)
    if cur <= 1: good.append((max(cur, F(0)), F(1)))
    return [(a, b) for a, b in good if 0 <= a <= b <= 1]

def deficiency_fires(T, H):
    """returns (l, budget) if the criterion fires on this split, else None."""
    h = len(H)
    if not (1 <= h <= 6): return None
    L = [v for v in T if v not in H]
    eta = (F(1, h + 1) - LEVEL) / max(H)
    l = 2 * eta
    budget = sum(F(int(l * v) + 1, 4 * v) for v in L)
    return (l, budget) if budget < l else None

def deficiency_witness(T, H):
    """build the witness the theorem promises, exactly."""
    h = len(H); L = [v for v in T if v not in H]
    g = good_set(H, F(1, h + 1))
    if not g: raise AssertionError(f"LRC({h+1}) failed on {H}")
    lo, hi = max(g, key=lambda p: p[1] - p[0]); t0 = (lo + hi) / 2
    assert all(nrm(F(v) * t0) >= F(1, h + 1) for v in H), \
        f"t0={t0} is NOT lonely for H={H} at 1/{h+1}"      # the check that caught the bug
    eta = (F(1, h + 1) - LEVEL) / max(H)
    lo_J, hi_J = t0 - eta, t0 + eta
    # remove the L bad sets from J, exactly
    cuts = []
    for v in L:
        for k in range(int(lo_J * v) - 1, int(hi_J * v) + 2):
            cuts.append((F(k, v) - LEVEL / v, F(k, v) + LEVEL / v))
    cuts.sort()
    cur = lo_J
    for a, b in cuts:
        if a > cur: return (cur + min(a, hi_J)) / 2
        cur = max(cur, b)
        if cur >= hi_J: break
    if cur < hi_J: return (cur + hi_J) / 2
    raise AssertionError(f"criterion fired but J fully covered: T={T} H={H}")

def part2():
    print("PART 2 -- the interval-deficiency criterion")
    print("  the single-gap ladder, H = the 7-k smallest speeds (floor terms dropped):")
    for k in range(1, 5):
        h = 7 - k
        print(f"    |L|={k}: sum_(i>{h}) 1/v_i  <  {k}/({8-k} v_{h})"
              f"      [l = {k}/(4*{8-k} v_{h})]")
    print()
    tests = [
        ("k=1  v7 > 7 v6",          [1, 2, 3, 4, 5, 6, 43]),
        ("k=1  v7 = 7 v6 (must NOT fire)", [1, 2, 3, 4, 5, 6, 42]),
        ("k=2  v6,v7 >> v5",        [1, 2, 3, 4, 5, 61, 401]),
        ("k=3  v5,v6,v7 >> v4",     [1, 2, 3, 4, 41, 97, 601]),
    ]
    for name, T in tests:
        T = sorted(T); hit = None
        for k in range(1, 5):
            H = T[:7 - k]
            r = deficiency_fires(T, H)
            if r: hit = (k, H, r); break
        if hit is None:
            print(f"  {name:<34} does not fire")
            continue
        k, H, (l, b) = hit
        t = deficiency_witness(T, H)
        ok = all(nrm(F(v) * t) >= LEVEL for v in T)
        m = min(nrm(F(v) * t) for v in T)
        print(f"  {name:<34} fires at |L|={k}, l={l}, budget={b} < l ; "
              f"t={t}  min||vt||={m}  {'LONELY OK' if ok else 'FAIL'}")
    print()

    # pruning power: how many random lacunary-at-one-place tuples are decided
    import random
    rng = random.Random(20260908)
    for k in (1, 2, 3):
        fired = ok = 0
        for _ in range(3000):
            base = sorted(rng.sample(range(1, 40), 7 - k))
            if reduce(gcd, base) == 0: continue
            top = []
            hi = max(base)
            for _ in range(k):
                hi = hi * rng.randint(3, 12) + rng.randint(0, 5); top.append(hi)
            T = sorted(set(base + top))
            if len(T) != 7: continue
            r = deficiency_fires(T, T[:7 - k])
            if not r: continue
            fired += 1
            t = deficiency_witness(T, T[:7 - k])
            if all(nrm(F(v) * t) >= LEVEL for v in T): ok += 1
        print(f"  |L|={k}: fired on {fired}/3000 sampled one-gap tuples, "
              f"witness verified {ok}  {'OK' if ok == fired else 'FAIL'}")
    print()

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    part1(N)
    part2()
