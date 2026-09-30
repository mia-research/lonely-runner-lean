"""E207 (2026-09-30): a stricter split: does it remove the spread-near-7 route?  (E206 step 1.)

Owner: "Yes try this" (E206's order: 1 a stricter split; 2 the crowd's mechanism; 3 crowds in the simplex).
DESIGN: the split re-splits the lower part at its own largest ratio while its spread exceeds s.  For every s in 1..7 the
split still applies to every arrangement (a single reading has spread 1): a design choice, not a narrowing.  A smaller s
gives a smaller slow part P, whose first clear interval [1, 7/sigma] (sigma <= s) is longer; at s = 1, P is the slowest
reading alone and its first interval is [1, 7].  Recorded per s: the index (P's clear interval holding the landing), and
for every later landing, P's spread and the fast part's shape (spread, tightest ratio), so the route is visible.
Checklist: object = the cascade's landing against P's own isolation intervals; no rate as answer; exceptions listed.
"""
import sys, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from wave_incident_v1 import lonely_components
from e151_block_v1 import trace

SS = (7, 5, 3, 2, 1)


def slow_part_s(S, s):
    X = sorted(S)
    while X[-1] > s * X[0]:
        r = [F(X[i + 1], X[i]) for i in range(len(X) - 1)]
        j = max(range(len(r)), key=lambda i: (r[i], -i))
        X = X[:j + 1]
    return X


def study(S):
    S = tuple(sorted(S)); d0 = S[0]
    ts, moves = trace(S)
    out = {}
    for s in SS:
        P = slow_part_s(S, s); Fp = [d for d in S if d not in P]
        Iv = lonely_components(list(P), F(1, 8 * d0), ts + F(2, d0))
        idx = next((i for i, (a, b) in enumerate(Iv) if a <= ts <= b), None)
        rat = [F(Fp[i + 1], Fp[i]) for i in range(len(Fp) - 1)]
        out[s] = (idx, F(P[-1], d0), (F(Fp[-1], Fp[0]) if Fp else None), (min(rat) if rat else None))
    return S, 8 * d0 * ts, out


def chunk(first):
    return [study((first,) + rest) for rest in itertools.combinations(range(first + 1, 25), 6)]


def report(name, rows, w):
    w("\n== %s: %d sets ==" % (name, len(rows)))
    for s in SS:
        idx = Counter(o[s][0] for S, R, o in rows)
        later = [(S, R, o[s]) for S, R, o in rows if o[s][0] != 0]
        w("  split threshold s = %d: index %s" % (s, dict(sorted(idx.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))))
        if later:
            w("    later landings: slow part spread %s; fast part spread %s; fast tightest ratio %s" % (
                dict(Counter(str(v[1]) for S, R, v in later).most_common(6)),
                dict(Counter(("%.1f" % float(v[2])) if v[2] else None for S, R, v in later).most_common(6)),
                dict(Counter(("%.2f" % float(v[3])) if v[3] else None for S, R, v in later).most_common(6))))
            w("    first later landings: %s" % [(S, str(R)) for S, R, v in later[:8]])


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('e207_split_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    rng = random.Random(13); cc1 = []
    while len(cc1) < 1000:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            cc1.append(T)
    rng = random.Random(29); cc2 = []
    while len(cc2) < 1000:
        T = tuple(sorted(rng.sample(range(1, 5001), 7)))
        if T[-1] > 24 * T[0]:
            cc2.append(T)
    with Pool(8) as pool:
        report('every 7-set of readings in 1..24', [r for part in pool.map(chunk, range(1, 19)) for r in part], w)
        report('late fine band shapes', pool.map(study, late_shapes()), w)
        report('Case C, readings <= 200', pool.map(study, cc1), w)
        report('Case C, readings <= 5,000', pool.map(study, cc2), w)
    out.close()
    print(open('e207_split_v1.out').read()[len(__doc__):])
