"""Is the number of laps set by how far the speeds are from an AP?

For each hard set (largest 41..60): the least push lap r (push_depth_v1: some q <= 8, e any multiple
of q, instant i/q + (r + 1/8)/e lonely), against
  gap     delta(S) = max_t min_d ||d t||   (1/8 exactly at the AP 1..7; larger = further from it),
  AP fit  the least, over integers D >= 1 and reorderings, of max_k |d_k - k*D| / D  -- how far the
          sorted disparities are from the multiples D, 2D, ..., 7D (Theorem 5's deviations e_k / d),
  spread  d_max / d_min,
  scale   M = e/q of the flank that certifies with the least r.
"""
import json, os, itertools
from statistics import mean
from collections import defaultdict
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
def lonely(S, e, j): return all(e <= d * (8 * j + 1) % (8 * e) <= 7 * e for d in S)
def least(S):
    best = None
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            M = e // q
            for r in range(M if best is None else min(M, best[0] + 1)):
                if any(lonely(S, e, i * M + r) for i in range(q)):
                    if best is None or r < best[0]: best = (r, M)
                    break
    return best
def gap(S):
    bn, bq = 0, 1
    for d, e in itertools.combinations(S, 2):
        for Q in (d + e, e - d):
            for m in range(Q):
                v = min(min(x * m % Q, Q - x * m % Q) for x in S)
                if v * bq > bn * Q: bn, bq = v, Q
    return bn / bq
def apfit(S):
    s = sorted(S); best = 9e9
    for D in range(1, s[-1] + 1):
        best = min(best, max(abs(d - (k + 1) * D) for k, d in enumerate(s)) / D)
    return best
rows = defaultdict(list)
for S in H:
    r, M = least(S)
    rows[r].append((gap(S), apfit(S), max(S) / min(S), M))
print("least lap r: sets | mean gap | mean AP-fit deviation | mean spread | mean flank scale e/q")
for r in sorted(rows):
    v = rows[r]
    print(f"   r = {r}: {len(v):5d} | {mean(x[0] for x in v):.3f} | {mean(x[1] for x in v):6.2f} | {mean(x[2] for x in v):6.1f} | {mean(x[3] for x in v):5.1f}")

# Control for the flank scale: only flanks with e/q >= 3, so laps 0, 1, 2 are all available.
def least_M3(S):
    best = None
    for q in range(2, 9):
        for e in S:
            if e % q or e // q < 3: continue
            M = e // q
            for r in range(M if best is None else min(M, best + 1)):
                if any(lonely(S, e, i * M + r) for i in range(q)):
                    if best is None or r < best: best = r
                    break
    return best
rows = defaultdict(list)
for S in H:
    r = least_M3(S)
    rows[r].append((apfit(S), max(S) / min(S)))
print("flanks with e/q >= 3 only -- least lap r: sets | mean AP-fit deviation | mean spread")
for r in sorted(rows, key=lambda x: (x is None, x)):
    v = rows[r]
    print(f"   r = {r}: {len(v):5d} | {mean(x[0] for x in v):6.2f} | {mean(x[1] for x in v):6.1f}")
