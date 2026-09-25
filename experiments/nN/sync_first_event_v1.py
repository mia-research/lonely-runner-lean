"""R' (read off the cascade, owner 2026-09-25): at the core's own first isolation event tau_C (the
core's cascade fixed point), do the block's offsets leave a gap > 1/4?

Exhaustive over the R cases of sync_block_v2 (f = 5 core 2, f = 6 core 1, speeds in [1,16]).  Exact.
tau_C is where some core runner reads exactly 1/8; the rule needs a point just inside the core's
cell, so the gap is tested at tau_C (gap > 1/4 there persists just inside by continuity).  Cases
where R' fails are listed with the core's LATER isolation events (its next lonely openings), to see
where the isolation actually goes.
"""
from fractions import Fraction as F
from itertools import combinations
from math import floor
from collections import Counter
def nd(x): x = x % 1; return min(x, 1 - x)
def cascade(S):
    t = F(1, 8 * min(S))
    while True:
        way = [d for d in S if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
def max_gap(pts):
    p = sorted(set(x % 1 for x in pts)); g = [p[i + 1] - p[i] for i in range(len(p) - 1)] + [1 - p[-1] + p[0]]
    return max(g)
n = ok = 0; fails = []; failg = Counter()
for f, c in ((5, 2), (6, 1)):
    for C in combinations(range(1, 17), c):
        tau = cascade(C)
        for off in combinations(range(1, 17), f - 1):
            n += 1; e = (0,) + off
            g = max_gap([x * tau for x in e])
            if g > F(1, 4): ok += 1
            else:
                failg[str(g)] += 1
                if len(fails) < 4: fails.append((C, e, tau, g))
print(f"[1,16]: {n} cases; offsets gapped (> 1/4) at the core's first isolation event: {ok};  not: {n - ok}")
print(f"   gaps where it fails: {sorted(failg.items())[:8]}")
for C, e, tau, g in fails: print(f"   core {C}, offsets {e}: core's first event tau = {tau}; offsets' largest gap there {g}")

# the failures: just inside the core's cell (t = tau + eps), and on the FULL set's cascade (N = 10^4)
def gap_just_after(e, tau):
    eps = F(1, 10**7); return max_gap([x * (tau + eps) for x in e])
inside = 0; rest = []
for f, c in ((5, 2), (6, 1)):
    for C in combinations(range(1, 17), c):
        tau = cascade(C)
        for off in combinations(range(1, 17), f - 1):
            e = (0,) + off
            if max_gap([x * tau for x in e]) > F(1, 4): continue
            if gap_just_after(e, tau) > F(1, 4): inside += 1
            else: rest.append((C, e, tau))
print(f"failures at tau itself: {inside + len(rest)};  gapped just inside the core's cell: {inside};  still not: {len(rest)}")
Nn = 10**4; laps = Counter(); where = Counter(); shown = 0
for C, e, tau in rest:
    S = sorted(set(list(C) + [Nn + x for x in e]))
    t = cascade(S)
    k = floor(t / tau) if tau else None
    cm = min(C)
    # which core isolation event is it near?  the core's lonely openings in order
    core_events = sorted({F(8 * j + 1, 8 * cc) for cc in C for j in range(0, 8 * cc) if all(nd(x * F(8 * j + 1, 8 * cc)) >= F(1, 8) for x in C)})
    idx = next((i for i, ev in enumerate(core_events) if ev > t), len(core_events)) - 1
    where[idx] += 1
    if shown < 6:
        shown += 1
        print(f"   core {C}, offsets {e}: full-set isolation t* = {float(t):.5f}; core's lonely openings {[str(x) for x in core_events[:5]]}...; t* follows core opening #{idx} ({core_events[idx] if idx >= 0 else None}); offsets' gap there {float(max_gap([x * core_events[idx] for x in e])):.3f}")
print(f"   the full set isolates just after the core's lonely opening number: {sorted(where.items())}")
