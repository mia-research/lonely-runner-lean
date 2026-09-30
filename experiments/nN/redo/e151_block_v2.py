"""E201b (2026-09-30): E151's statement, refined after the three questions on v1's exceptions.

v1 (e151_block_v1): every exception (231 + 6 + 3) had a slow part of spread 7 or just under, whose same-lap block B_0 is a
point or tiny; its top reading moves to its next lap while the rest of the slow part is still on lap 0, and the landing
follows that top reading's own exit.  So the right object is the slow part's OWN clear intervals (its isolation
intervals at 1/8, in time order from the bound: boundaries are its own exits and entries), not only its same-lap blocks.
REFINED STATEMENT: the cascade lands inside the slow part's first clear interval, or else, after a move set by the slow
part itself, inside its second.  (For a slow part of one reading these are v1's B_0 and B_1.)
Derived, unchanged: inside a clear interval of P only fast readings can be in the slot (D1).

v1's text follows.

E201 (2026-09-30): E151's statement in the owner's form, designed, then run against the cascade.

Owner: "yes, design E151's statement in that form first and then run it".  Map: CASCADE_DESIGN_v2 §3, §4, §7; the
gapless structure of E200.

DESIGN
  The split, gapless by construction.  Split the readings at the largest consecutive ratio; if the part below has spread
  above 7, split that part again at its own largest ratio; repeat.  This stops (a single reading has spread 1), so every
  arrangement gets a SLOW PART P (the lowest group, spread <= 7, AP-like at d_min's scale) and a FAST PART F (the rest).
  P's BLOCKS: B_k = [(8k+1)/(8 d_min), (8k+7)/(8 p_top)], for every lap k with p_top/d_min <= (8k+7)/(8k+1); P is clear
  throughout each B_k (`SlowBlockN.slow_clear_lap`, proved).
  Derived: (D1) inside a block only fast readings can be in the subject's slot, so every cascade move made inside a block
  is a move of F alone: there the cascade IS the fast part's own push; (D2) on a block the whole question is F's
  (`exists_block_iff_fast_lap`, proved).
  THE STATEMENT (a place, named by P's readings): the cascade lands inside P's first block B_0, as F's own push; or else,
  after a move set by P itself between B_0 and B_1, inside B_1 (E154's pattern: the slow runner sets one move itself and
  the crowd lands in the second block).
  Frame checks: the place is a block of the slow part, given by its readings; the push is the cascade itself (D1); no
  count of moves, no rate, no instant family; "first isolation" is not used (the statement is where the cascade lands).

RUN (exact, Fractions).  Per set: P and F; the block holding the landing (0, 1, 2, ..., or none); the moves between B_0
and B_1 and who set them; the derived check D1 on every move; the landing checked lonely.  Every set outside the
statement is listed individually, with its trace, for the three questions (M3).
Populations: every 7-set of readings in 1..24 (346,104); the late fine band shapes (coverB_fine_v1.late_shapes); Case C
samples (spread above 24: 1,000 with readings <= 200, seed 13; 1,000 with readings <= 5,000, seed 29).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8, next_opening
from wave_incident_v1 import lonely_components


def slow_part(S):
    X = sorted(S)
    while X[-1] > 7 * X[0]:
        r = [F(X[i + 1], X[i]) for i in range(len(X) - 1)]
        j = max(range(len(r)), key=lambda i: (r[i], -i))
        X = X[:j + 1]
    return X


def blocks(P, kmax=40):
    d0, top = P[0], P[-1]
    out = []
    for k in range(kmax):
        lo, hi = F(8 * k + 1, 8 * d0), F(8 * k + 7, 8 * top)
        if lo > hi:
            break
        out.append((k, lo, hi))
    return out


def trace(S):
    t = F(1, 8 * min(S)); moves = []
    for _ in range(100000):
        way = [d for d in S if cd(d * t) < E8]
        if not way:
            return t, moves
        nx = max(next_opening(d, t) for d in way)
        setters = [d for d in way if next_opening(d, t) == nx]
        moves.append((t, tuple(way), tuple(setters), nx))
        t = nx
    raise RuntimeError('no landing within the move cap')


def where(t, B):
    for k, lo, hi in B:
        if lo <= t <= hi:
            return k
    return None


def study(S):
    S = tuple(sorted(S))
    P = slow_part(S); Fp = [d for d in S if d not in P]
    ts, moves = trace(S)
    B = [(i, a, b) for i, (a, b) in enumerate(lonely_components(list(P), F(1, 8 * P[0]), ts + F(2, P[0])))]
    lonely = all(cd(d * ts) >= E8 for d in S)
    d1 = all(set(way) <= set(Fp) for t, way, st, nx in moves if where(t, B) is not None)
    kb = where(ts, B)
    between = []
    if len(B) >= 2:
        between = [(t, st) for t, way, st, nx in moves if B[0][2] < t < B[1][1] or (t == B[0][2] and any(s in P for s in way))]
    set_by_P = any(any(s in P for s in st) for t, st in between)
    return dict(S=S, P=tuple(P), nF=len(Fp), nB=len(B), kb=kb, lonely=lonely, d1=d1, set_by_P=set_by_P,
                R=8 * S[0] * ts, ts=ts, nmoves=len(moves),
                trace=[(t, way, st) for t, way, st, nx in moves][-8:] if kb not in (0, 1) else None)


def chunk(first):
    return [study((first,) + rest) for rest in itertools.combinations(range(first + 1, 25), 6)]


def report(name, rows, w):
    w("\n== %s: %d sets ==" % (name, len(rows)))
    w("  CHECK the landing is lonely: %d violations" % sum(not r['lonely'] for r in rows))
    w("  CHECK D1 (moves inside a block are the fast part's alone): %d violations" % sum(not r['d1'] for r in rows))
    w("  slow part size: %s; fast part size: %s" % (dict(sorted(Counter(len(r['P']) for r in rows).items())),
                                                   dict(sorted(Counter(r['nF'] for r in rows).items()))))
    w("  the slow part's clear interval holding the landing (0 = first): %s" %
      dict(sorted(Counter(r['kb'] for r in rows).items(), key=lambda kv: (kv[0] is None, kv[0] if kv[0] is not None else 0))))
    b1 = [r for r in rows if r['kb'] == 1]
    w("  landings in the second interval: %d; with a move set by the slow part between the first two: %d" %
      (len(b1), sum(r['set_by_P'] for r in b1)))
    exc = [r for r in rows if r['kb'] not in (0, 1)]
    w("  OUTSIDE the statement (not in the first two intervals): %d" % len(exc))
    for r in exc[:40]:
        w("    %s  P %s  blocks %d  landing block %s  R* %s  moves %d" % (r['S'], r['P'], r['nB'], r['kb'], r['R'], r['nmoves']))
        for t, way, st in r['trace']:
            w("        move at %s: in the slot %s, setter %s" % (t, way, st))


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('e151_block_v2.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
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
        rowsA = [r for part in pool.map(chunk, range(1, 19)) for r in part]
        report('every 7-set of readings in 1..24', rowsA, w)
        report('late fine band shapes', pool.map(study, late_shapes()), w)
        report('Case C, readings <= 200 (seed 13)', pool.map(study, cc1), w)
        report('Case C, readings <= 5,000 (seed 29)', pool.map(study, cc2), w)
    out.close()
    print(open('e151_block_v2.out').read()[len(__doc__):])
