#!/usr/bin/env python3
"""Observation only. The units / zero-divisor structure of Z/6 along the cascade's own walk on primitive SixResidual
(max <= 40, from six_cascade_observe_v1.tsv), exact Fractions.
Classes by d mod 6: U (1,5, units), E (2,4), T (3), M (0, multiples of 6). Zero-divisor content of a set = (#M+T, #M+E)
= (multiples of 3, multiples of 2): Renault's dispatch coordinates.
At every walk instant t_i (start 1/(6 v1), then each move; the last is lonely):
  - the sixth-shift frame: for u = 0..5, which runners are within 1/6 of a lap point at t_i + u/6 (exact);
    free shifts F_i = {u : t_i + u/6 lonely}; u = 1, 5 are the event shifts (units of Z/6), 2, 3, 4 non-events.
  - for each blocked (runner, u): its class. Recorded: whether events are blocked only by U and non-events only by
    E/T/M (E45's clean split) in each frame; and who blocks the events.
  - the move's setter class, and the classes of the runners in the way.
Questions: (a) at which walk instant does the sixth-shift frame first contain a lonely instant, against the end;
(b) how the frames that hold no lonely instant are blocked, by class; (c) setter classes; all by zero-divisor content."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
SIX = F(1, 6)
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def cls(d): return {0: "M", 3: "T", 2: "E", 4: "E"}.get(d % 6, "U")
def walk(S):
    t = F(1, 6 * S[0]); inst = [t]; setters = []; inway = []
    while True:
        blk = [d for d in S if cd(d * t) < SIX]
        if not blk: return inst, setters, inway
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d)
        inway.append(tuple(sorted(cls(d) for d in blk)))
        t = best[0]; inst.append(t); setters.append(cls(best[1]))
first_free = defaultdict(Counter); frames_full = defaultdict(Counter); clean = defaultdict(Counter)
ev_blockers = defaultdict(Counter); setter = defaultdict(Counter); inway_c = defaultdict(Counter)
final_free = defaultdict(Counter); final_free_set = defaultdict(Counter); nz = Counter()
for S in rows:
    m3 = sum(d % 3 == 0 for d in S); m2 = sum(d % 2 == 0 for d in S); key = f"m3={m3},m2={m2}"; nz[key] += 1
    inst, st, iw = walk(S); m = len(inst) - 1
    ff = None
    for i, t in enumerate(inst):
        blocked = {u: [d for d in S if cd(d * (t + u * SIX)) < SIX] for u in range(6)}
        free = [u for u in range(6) if not blocked[u]]
        if free and ff is None: ff = i
        if i == m:
            final_free[key][len(free)] += 1; final_free_set[key][tuple(free)] += 1
        if not free:
            frames_full[key]["frames"] += 1
            ok = all(cls(d) == "U" for u in (1, 5) for d in blocked[u]) and \
                 all(cls(d) != "U" for u in (2, 3, 4) for d in blocked[u])
            clean[key][ok] += 1
            for u in (1, 5):
                ev_blockers[key][tuple(sorted(set(cls(d) for d in blocked[u])))] += 1
    first_free[key][("at end" if ff == m else f"{m - ff} instants before end")] += 1
    for s in st: setter[key][s] += 1
    for w in iw: inway_c[key][w] += 1
tot = Counter()
print(f"sets: {len(rows)}; by zero-divisor content (multiples of 3, of 2): {dict(sorted(nz.items()))}")
for key in sorted(nz):
    print(f"== {key} ({nz[key]})")
    print("   (a) first walk instant whose sixth-shift frame holds a lonely instant:", dict(first_free[key].most_common()))
    print("       free shifts at the final instant (count):", dict(sorted(final_free[key].items())),
          " commonest sets:", final_free_set[key].most_common(4))
    print(f"   (b) frames with no lonely shift: {frames_full[key]['frames']}; E45 clean split holds in {clean[key][True]}")
    print("       classes blocking the event shifts 1/6, 5/6 in those frames:", ev_blockers[key].most_common(6))
    print("   (c) setter classes:", dict(setter[key].most_common()), " in-the-way class sets:", inway_c[key].most_common(5))
    for k in ("U", "E", "T", "M"): tot[k] += setter[key][k]
print("all setters:", dict(tot))
