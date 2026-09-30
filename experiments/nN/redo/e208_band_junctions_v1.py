"""E208 (2026-09-30): E125's question in the band: why the cascade's chain cannot cover both copies; the junctions split
into the grid's part and the deviation's part.

Owner: "yes, design E125's question in the band first, then run it / Then review if we need to prove it in lean now".

DESIGN (units: readings s_i in units of d_min, R = 8 d_min t; the band: 7 < s_6 < 9)
  The chain (E122, E125, derived from the cascade's definition): reading s blocks the open windows ((8k-1)/s, (8k+1)/s);
  each move goes to the end of the latest-ending window containing the current R; consecutive setters (a, lap k) and
  (b, lap l) JOIN iff b's window contains a's exit: slack J = s_b (8k+1) - s_a (8l-1) > 0.  The landing is an exit no
  window contains: for the next window of each other reading c (lap l_c), the slack is <= 0; the one reached soonest in time (the
  queue front, E204) is the BREAK.
  The reference grid (the owner's AP/grid, E128): the slowest reading's own grid, s_i = n_i + delta_i with n_i the
  nearest whole number.  Every slack splits exactly, linearly in the deviations:
      J = [n_b (8k+1) - n_a (8l-1)]  +  [delta_b (8k+1) - delta_a (8l-1)]
          (the GRID's slack: a whole number)   (the DEVIATION's part: amplified by the laps)
  For the AP the grid slack of its own junctions is exactly 0 (windows touch).
  THE QUESTION, in the owner's terms: is the band's landing where the grid itself has a gap (break with grid slack < 0),
  or where the deviation breaks a junction the grid holds tight (grid slack = 0) or open (> 0)?  And what carries the
  chain: grid overlaps (> 0), or tight grid junctions held by the deviation?
  Checklist: the object is the cascade's own chain; the grid is the arrangement's own (through d_min); the split is exact
  algebra (a check); no instant family; no rate as the answer (the kinds are listed, the exceptions shown); no first
  isolation.
RUN (exact) on every integer band set with readings <= 28 (7 d_min < d_max < 9 d_min) and the late fine band shapes.
"""
import sys, itertools, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from e151_block_v1 import trace


def study(T):
    T = tuple(sorted(T)); d0 = T[0]
    s = [F(d, d0) for d in T]
    n = [round(x) for x in s]
    dl = [x - q for x, q in zip(s, n)]
    idx = {d: i for i, d in enumerate(T)}
    ts, moves = trace(T)
    Rl = 8 * d0 * ts
    setters = []
    for t, way, st, nx in moves:
        a = idx[min(st)]
        k = round(s[a] * 8 * d0 * nx / 8 - F(1, 8))       # nx = (8k+1)/(8 s_a d0)
        setters.append((a, k))
    joins = []
    for (a, k), (b, l) in zip(setters, setters[1:]):
        g = n[b] * (8 * k + 1) - n[a] * (8 * l - 1)
        dv = dl[b] * (8 * k + 1) - dl[a] * (8 * l - 1)
        joins.append((g, dv))
    brk = None
    if setters:
        h, K = setters[-1]
        best = None
        for c in range(7):
            if c == h:
                continue
            X = s[c] * (8 * K + 1) / s[h]                 # c's position at the exit, in eighths
            l = math.floor((X + 1) / 8)                   # c's next window: the least l with 8l - 1 > X
            while 8 * l - 1 <= X:
                l += 1
            wait = (8 * l - 1 - X) / s[c]                 # time (in R) until c reaches that window: the queue front is least
            J = s[c] * (8 * K + 1) - s[h] * (8 * l - 1)
            if best is None or wait < best[5]:
                g = n[c] * (8 * K + 1) - n[h] * (8 * l - 1)
                best = (J, g, J - g, c, l, wait)
        brk = best
    return dict(T=T, copy=(0 if Rl <= 7 else 1), R=Rl, joins=joins, brk=brk, n=n)


def chunk(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 29), 6):
        T = (first,) + rest
        if 7 * T[0] < T[-1] < 9 * T[0]:
            r = study(T)
            if r['brk'] is not None:
                out.append(r)
    return out


def sign(x):
    return '<0' if x < 0 else ('=0' if x == 0 else '>0')


def report(name, rows, w):
    w("\n== %s: %d band sets with a chain ==" % (name, len(rows)))
    w("  landing copy (0 = [1,7], 1 = [9,15]): %s" % dict(Counter(r['copy'] for r in rows)))
    J = [j for r in rows for j in r['joins']]
    w("  CHECK every join has total slack > 0: %d violations" % sum(1 for g, d in J if g + d <= 0))
    w("  joins by grid slack: %s" % dict(Counter(sign(g) for g, d in J)))
    w("  joins with grid slack 0 (tight on the grid): the deviation's part %s" % dict(Counter(sign(d) for g, d in J if g == 0)))
    w("  joins with grid slack < 0 (a grid gap bridged by the deviation): %d" % sum(1 for g, d in J if g < 0))
    B = [r['brk'] for r in rows]
    w("  CHECK every break has total slack <= 0: %d violations" % sum(1 for b in B if b[0] > 0))
    w("  the break at the landing, by grid slack: %s" % dict(Counter(sign(b[1]) for b in B)))
    for cp in (0, 1):
        Bc = [r['brk'] for r in rows if r['copy'] == cp]
        if Bc:
            w("    landing in copy %d: grid slack of the break %s; grid-tight breaks with the deviation's part %s" %
              (cp, dict(Counter(sign(b[1]) for b in Bc)), dict(Counter(sign(b[2]) for b in Bc if b[1] == 0))))
    ex = [r for r in rows if r['brk'][1] > 0][:10]
    w("  breaks where the grid overlaps (> 0) and the deviation breaks it, examples: %s" %
      [(r['T'], str(r['R']), r['brk'][1], str(r['brk'][2])) for r in ex])


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('e208_band_junctions_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    with Pool(8) as pool:
        report('every integer band set, readings <= 28', [r for part in pool.map(chunk, range(1, 23)) for r in part], w)
        report('late fine band shapes', [r for r in pool.map(study, late_shapes()) if r['brk'] is not None], w)
    out.close()
    print(open('e208_band_junctions_v1.out').read()[len(__doc__):])
