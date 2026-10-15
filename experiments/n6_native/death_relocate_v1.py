#!/usr/bin/env python3
"""Observation only. Owner: at a death along the AP -> set path, is the isolation relocated to the next isolation
(the next lonely instant after the dying one) rather than restarted elsewhere? Uses slot_deform_v1's exact path
segments (lap vector m held while alive; restart = earliest lonely instant). For each death after s = 0, at v(s*):
  L_old = the dying instant (its interval is one point); E = the earliest lonely instant just past s* (the restart);
  N = the first lonely instant after L_old just past s* (cascade started at L_old).
Recorded: E against L_old (earlier / later); E == N; whether N's lap vector is alive at s* itself (relocation without
a gap); lap change N - m; and, for the fold view, c mod 6 of each instant written as c/q with speeds scaled to integers
(which order-6 ideal event, p = 1 or 5, the instant lies over)."""
import sys
from fractions import Fraction as F
from collections import Counter
from math import lcm
sys.argv = ["x"]
import importlib.util
sp = importlib.util.spec_from_file_location("sd", "slot_deform_v1.py"); sd = importlib.util.module_from_spec(sp); sp.loader.exec_module(sd)
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
STEP = int(sys.argv[1]) if len(sys.argv) > 1 else 4
def casc_from(v, t):
    while True:
        nxt = [F(6 * round(d * t) + 1, 6 * d) for d in v if abs(d * t - round(d * t)) < F(1, 6)]
        if not nxt: return t
        t = max(nxt)
def fold(v, t):
    D = lcm(*[x.denominator for x in v]); u = t / D   # integer speeds D*v, instant t/D
    return u.numerator % 6
rel = Counter(); eqN = Counter(); gap = Counter(); dm = Counter(); fl = Counter(); n = 0
for S in rows[::STEP]:
    R = sd.run_path(S, Counter(), Counter())
    segs = R["segs"]
    for (m, a, hi), (m2, a2, hi2) in zip(segs, segs[1:]):
        if hi == 0: continue
        n += 1
        v = sd.vs(S, hi); Lold = sd.Lm(v, m)
        vn = sd.vs(S, hi + sd.EPS)
        E, _ = sd.cascade(vn); N = casc_from(vn, Lold)
        rel["restart earlier than dying instant" if E < Lold else "restart later"] += 1
        eqN[E == N] += 1
        mN = sd.laps(vn, N)
        rng = sd.alive_range(S, mN); gap[rng is not None and rng[0] <= hi] += 1
        dm[tuple(x - y for x, y in zip(mN, m))] += 1
        fl[(fold(v, Lold), fold(v, sd.Lm(v, mN)) if rng and rng[0] <= hi else None)] += 1
print(f"deaths after s=0 on every {STEP}th path: {n}")
print("restart (earliest lonely instant) vs dying instant:", dict(rel))
print("restart equals the next lonely instant after the dying one:", dict(eqN))
print("next lonely instant's lap vector already alive at the death s (no gap):", dict(gap))
print("lap change to the next isolation (N - m), commonest:", dm.most_common(12))
print("ideal event (c mod 6) of (dying instant, next isolation's instant at the death s):", fl.most_common(8))
