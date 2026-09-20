import re
"""
lrc_adjoin_vs_translate_v1.py  (2026-09-12)

Decides GLOBAL ISOLATION for a given speed set, exactly (Fraction/int only).

Global isolation for a set V of n distinct speeds:
    exists t with  ||(v_i - v_j) t|| >= 1/n  for every pair i<j,
where ||x|| = distance to the nearest integer.

Two INDEPENDENT implementations:

  [A] residue criterion -- translate so one runner is 0, divide by
      g = gcd of the pairwise differences; global isolation holds iff the
      reduced speeds form a COMPLETE RESIDUE SYSTEM mod n.

  [B] exact boundary-set brute force -- the feasible set for t is closed and
      its boundary points all satisfy ||d t|| = 1/n for some pairwise
      difference d, i.e. t = (k +- 1/n)/d.  Collect every such t in one
      period, evaluate min-gap at each candidate AND at each midpoint
      between consecutive candidates (entry, exit, and interior -- never the
      centre alone).  Reports the witness t when feasible.

Purpose: the two configurations {2,4,6,104} (n=4) and {0,2,4,6,104} (n=5)
differ only by an ADJOINED stationary runner and get OPPOSITE answers.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations


def frac_dist(x: F) -> F:
    """distance from x to the nearest integer, exact"""
    r = x - (x.numerator // x.denominator)          # r in [0,1)
    return min(r, 1 - r)


def min_gap(speeds, t: F) -> F:
    return min(frac_dist((a - b) * t) for a, b in combinations(speeds, 2))


# ---------------------------------------------------------------- [A]
def residue_criterion(speeds):
    n = len(speeds)
    assert len(set(speeds)) == n, "speeds must be distinct"
    ref = speeds[0]
    shifted = [v - ref for v in speeds]
    g = reduce(gcd, [abs(x) for x in shifted])
    reduced = [x // g for x in shifted]
    residues = sorted(x % n for x in reduced)
    complete = residues == list(range(n))
    return complete, g, reduced, residues



def _extremal_candidates(speeds):
    """Candidate times for the MAXIMUM of the min-gap.

    The min-gap is a minimum of linear functions, hence concave on each cyclic-order
    cell, so its maximum can sit strictly INSIDE a cell.  BSM boundary times (where some
    pair's gap equals the threshold) are event-complete for the PREDICATE only; they do
    not contain the interior maximum.  The interior maxima live at t = m/delta with
    delta a SIGNED difference of SIGNED differences.
    """
    deltas = set()
    for a in speeds:
        for b in speeds:
            for c in speeds:
                for d in speeds:
                    delta = (a - b) - (c - d)
                    if delta: deltas.add(abs(delta))
    out = set()
    for delta in deltas:
        for m in range(delta + 1):
            out.add(F(m, delta))
    return out

# ---------------------------------------------------------------- [B]
def brute_force(speeds):
    n = len(speeds)
    thr = F(1, n)
    diffs = sorted({abs(a - b) for a, b in combinations(speeds, 2)})
    period = F(1, reduce(gcd, diffs))            # positions repeat with this period
    cands = set()
    for d in diffs:
        k = 0
        while F(k, 1) / d <= period + 1:
            for s in (thr, -thr):
                t = (F(k) + s) / d
                if 0 <= t <= period:
                    cands.add(t)
            k += 1
    cands.add(F(0))
    cands.add(period)
    pts = sorted(cands)
    # BSM boundary times decide the PREDICATE (event-complete for "min-gap >= thr").
    feasible = any(min_gap(speeds, t) >= thr
                   for t in list(pts) + [(pts[i] + pts[i+1]) / 2
                                         for i in range(len(pts) - 1)])
    # The MAXIMUM needs the signed difference-of-differences set -- a BSM cell midpoint
    # is not where the concave maximum sits.  See _extremal_candidates.
    best_t, best = None, F(-1)
    for t in _extremal_candidates(speeds) | set(pts):
        if t < 0 or t > period: continue
        m = min_gap(speeds, t)
        if m > best:
            best, best_t = m, t
    assert feasible == (best >= thr), "predicate and extremum disagree"
    return feasible, best, best_t


def report(speeds):
    n = len(speeds)
    complete, g, reduced, residues = residue_criterion(speeds)
    feasible, best, best_t = brute_force(speeds)
    print(f"V = {speeds}")
    print(f"  n (runners GIVEN, counted) = {n}   threshold 1/n = {F(1,n)}")
    print(f"  g = {g}   reduced = {reduced}   residues mod {n} = {residues}"
          f"   -> {'COMPLETE' if complete else 'NOT complete'}")
    print(f"  [A] residue criterion : global isolation = {complete}")
    print(f"  [B] exact brute force : global isolation = {feasible}"
          f"   max-min-gap = {best} at t = {best_t}")
    if feasible:
        print(f"      positions at t={best_t}: "
              f"{[str((v*best_t) % 1) for v in speeds]}")
    assert complete == feasible, "IMPLEMENTATIONS DISAGREE"
    print("  [A] == [B] ok")
    print()
    return complete


# ---------------------------------------------------------------- per-runner LRC
def lonely(speeds, i):
    """does runner i alone reach gap >= 1/n from all others at SOME time"""
    n = len(speeds); thr = F(1, n)
    ds = sorted({abs(speeds[j] - speeds[i]) for j in range(n) if j != i})
    period = F(1, reduce(gcd, ds)); c = {F(0), period}
    for dd in ds:
        k = 0
        while F(k) / dd <= period + 1:
            for s in (thr, -thr):
                t = (F(k) + s) / dd
                if 0 <= t <= period: c.add(t)
            k += 1
    pts = sorted(c); probe = pts + [(pts[a]+pts[a+1])/2 for a in range(len(pts)-1)]
    best, bt = F(-1), None
    for t in probe:
        m = min(frac_dist((speeds[j]-speeds[i])*t) for j in range(n) if j != i)
        if m > best: best, bt = m, t
    return best >= thr, best, bt


def lrc(speeds):
    """LRC: EACH runner lonely at SOME (possibly different) time. Weaker than
    global isolation, which demands ONE time for all."""
    out = [lonely(speeds, i) for i in range(len(speeds))]
    return all(o[0] for o in out), out


import sys
if len(sys.argv) > 1:
    V = [int(x) for x in re.split(r"[,\s]+", " ".join(sys.argv[1:]).strip("{}[]() ")) if x]
    report(V)
    ok, out = lrc(V)
    print(f"  LRC (each lonely at SOME time, weaker) = {ok}")
    for v, (f, b, t) in zip(V, out):
        print(f"      runner {v}: lonely={f} max-min-gap={b} at t={t}")
    sys.exit(0)

print("=== the adjoin-vs-translate pair ===\n")
a = report([2, 4, 6, 104])              # as GIVEN: 4 runners
b = report([0, 2, 4, 6, 104])           # a stationary runner ADJOINED: 5 runners
print(f"same speeds, opposite answers: {a} vs {b} -> {a != b}\n")

print("=== BOUNDARY: global isolation is STRICTLY STRONGER than LRC ===\n")
for V in ([2,4,6,104], [0,2,4,6,104]):
    ok,_ = lrc(V)
    gi,_,_,_ = residue_criterion(V)
    print(f"  V={V}  n={len(V)}  global isolation={gi}   LRC={ok}")
print("  -> the 5-runner set FAILS global isolation and SATISFIES LRC.")
print("     'not a complete residue system' is NOT an LRC counterexample.\n")

print("=== translation is free: every reference gives the same verdict ===\n")
V = [2, 4, 6, 104]
for ref in V:
    W = [v - ref for v in V]
    c, g, red, res = residue_criterion(W)
    f, best, bt = brute_force(W)
    print(f"  reference {ref}: shifted {W}  n={len(W)}  residues {res}  isolation={c} (bf {f})")
