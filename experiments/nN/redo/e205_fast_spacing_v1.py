"""E205 (2026-09-30): the fast part's isolation spacing, against the slow part's intervals.

Owner: "yes, design the fast part's isolation spacing first, then run it / Then lets review carefully if we are
progressing and check against drift".

DESIGN (units R = 8 d_min t; P the slow part of spread sigma <= 7, F the fast part; E201's split)
  Objects: F's own ISOLATION INTERVALS (F alone lonely at 1/8: the fast part's own isolation events, which exist by the
  native lower order); their GAPS; F's natural unit, one lap of its slowest reading, 8 d_min / f_1 in R.
  FORCED (checks, M4): P is clear on its first interval I0 = [1, 7/sigma], so the landing is in I0 iff F has an isolation
  point in I0; the gap of F containing R = 1 is exactly F's push from the bound (E202).
  CONTENT (recorded, not assumed): the spacing of F's isolation across I0 and across P's first period, in F-laps, read
  against F's own structure: its spread sigma_F = f_top / f_1 and its tightest internal ratio (a CROWD: readings close in
  ratio, moving nearly together).  The hypothesis to test: a spread F has short gaps (few F-laps); a crowded F blocks the
  slot for long stretches (sparse isolation), which is what sends the late shapes to P's second interval.
  Checklist: the objects are the fast part's own isolation events and the slow part's intervals; gaps recorded, never
  bounded as the argument; no rate as the answer; no instant family; no first isolation.
RUN (exact).  Per set with a fast part: F's isolation intervals over [1, 9] and the landing's interval; the largest gap
of F inside [1, max(7/sigma, the landing)] in F-laps; F's number of isolation intervals inside I0; sigma_F and F's
tightest ratio; the index (E201).  Checks: index 0 iff F has an isolation point in I0 (forced).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8
from wave_incident_v1 import lonely_components
from e151_block_v1 import slow_part, trace


def study(S):
    S = tuple(sorted(S)); d0 = S[0]
    P = slow_part(S); Fp = [d for d in S if d not in P]
    if not Fp:
        return None
    sigma = F(P[-1], d0); f1 = Fp[0]
    ts, moves = trace(S)
    Rl = 8 * d0 * ts
    t_of = lambda R: R / (8 * d0)
    Pi = lonely_components(list(P), F(1, 8 * d0), ts + F(2, d0))
    idx = next((i for i, (a, b) in enumerate(Pi) if a <= ts <= b), None)
    hi = max(F(7) / sigma, Rl, F(9))
    J = [(8 * d0 * a, 8 * d0 * b) for a, b in lonely_components(Fp, t_of(F(1)), t_of(hi))]
    I0 = (F(1), F(7) / sigma)
    inI0 = [j for j in J if j[1] >= I0[0] and j[0] <= I0[1]]
    lap = F(8 * d0, f1)                                  # one F-lap in R
    window_end = max(I0[1], Rl)
    pts = [F(1)] + [x for j in J for x in j if x <= window_end] + [window_end]
    gaps = []
    prev = F(1) if not (J and J[0][0] <= 1) else J[0][1]
    for a, b in J:
        if a > window_end:
            break
        if a > prev:
            gaps.append(a - prev)
        prev = max(prev, b)
    gmax = max(gaps) / lap if gaps else F(0)
    g0 = (J[0][0] - 1) / lap if J and J[0][0] > 1 else F(0)            # F's gap at the start, in F-laps
    ratios = [F(Fp[i + 1], Fp[i]) for i in range(len(Fp) - 1)]
    return dict(S=S, P=tuple(P), Fp=tuple(Fp), sigma=sigma, idx=idx, nI0=len(inI0), gmax=gmax, g0=g0,
                sigmaF=F(Fp[-1], f1), tight=min(ratios) if ratios else None, rho=F(f1, P[-1]),
                check=(idx == 0) == bool(inI0))


def chunk(first):
    return [r for r in (study((first,) + rest) for rest in itertools.combinations(range(first + 1, 25), 6)) if r]


def band(x, edges):
    for e in edges:
        if x <= e:
            return "<= %s" % e
    return "> %s" % edges[-1]


def report(name, rows, w):
    rows = [r for r in rows if r]
    w("\n== %s: %d sets with a fast part ==" % (name, len(rows)))
    w("  CHECK index 0 iff F has an isolation point in the slow part's first interval (forced): %d violations" % sum(not r['check'] for r in rows))
    w("  index: %s" % dict(sorted(Counter(r['idx'] for r in rows).items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
    w("  F's gap at the start (F-laps), index 0 / later:")
    for lbl, grp in (('index 0', [r for r in rows if r['idx'] == 0]), ('later', [r for r in rows if r['idx'] != 0])):
        w("    %s: %s" % (lbl, dict(sorted(Counter(band(float(r['g0']), [0, 0.25, 0.5, 1, 2, 4, 8]) for r in grp).items()))))
    w("  F's number of isolation intervals inside the first interval (index-0 sets): %s" %
      dict(sorted(Counter(min(r['nI0'], 10) for r in rows if r['idx'] == 0).items())))
    w("  F's spread sigma_F, index 0 / later:")
    for lbl, grp in (('index 0', [r for r in rows if r['idx'] == 0]), ('later', [r for r in rows if r['idx'] != 0])):
        w("    %s: %s" % (lbl, dict(sorted(Counter(band(float(r['sigmaF']), [1.5, 2, 3, 4, 7, 20]) for r in grp).items()))))
    w("  F's tightest internal ratio, index 0 / later:")
    for lbl, grp in (('index 0', [r for r in rows if r['idx'] == 0]), ('later', [r for r in rows if r['idx'] != 0])):
        w("    %s: %s" % (lbl, dict(sorted(Counter(band(float(r['tight']), [1.05, 1.1, 1.2, 1.5, 2]) for r in grp if r['tight']).items()))))
    w("  the slow part's spread sigma of the later landings: %s" % dict(Counter(str(r['sigma']) for r in rows if r['idx'] != 0).most_common(8)))


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('e205_fast_spacing_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
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
    print(open('e205_fast_spacing_v1.out').read()[len(__doc__):])
