"""E204 (2026-09-30): the passage-end configuration: the entering queue at every move of the cascade.

Owner: "yes, design the passage-end configuration first, then run it".

DESIGN (the cascade's own objects)
  At a move starting at t, the readings not in the subject's slot form the ENTERING QUEUE: each approaches the entering
  edge (position 7/8 of its lap) and reaches it after T_c = (7/8 - frac(c t))/c.  The move lasts D = (the setter's exit) - t.
  FORCED (the cascade's rule restated, M4): a queue reading is carried in during the move iff T_c < D and it has not left
  again by the move's end; a reading already in the slot at the move's start can also be carried in again if it is fast
  enough to leave and re-enter.  Both edge cases are counted, not treated as violations.
  CONTENT (not forced; recorded):
    C1 the conveyor: is the next setter the queue FRONT (least T_c) of the previous move?  Not forced: when several are
       carried in, the latest exit sets the next move.
    C2 cycling: in each chain, which readings set moves and how often; whether the readings that keep the relay going
       are the fast ones coming round again.
    C3 the end: at the landing, the front's identity (rank), and its margin T_front / D (> 1: it arrives after the
       setter leaves; the isolation lasts until it enters).
  Checklist: the queue, T_c, D and the carry-ins are the cascade's objects; D and T are recorded per move, never argued
  monotone (F1); no rate is the answer; no instant family; no first isolation.
RUN (exact) on relays: every chain to 24 with at least three passages (E203), the late fine band shapes, Case C chains.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8
from e151_block_v1 import trace
from e203_sweep_v1 import study as passages_of


def queue(S, t, way):
    out = []
    for c in S:
        if c in way:
            continue
        p = c * t - math.floor(c * t)
        out.append(((F(7, 8) - p) / c, c))
    return sorted(out)


def study(S, min_passages=3):
    S = tuple(sorted(S))
    ps = passages_of(S)
    if ps is None or ps['n_pass'] < min_passages:
        return None
    ts, moves = trace(S)
    rank = {d: i for i, d in enumerate(S)}
    rows = []
    for i, (t, way, st, nx) in enumerate(moves):
        D = nx - t
        q = queue(S, t, way)
        Tf, front = q[0]
        arrivals = moves[i + 1][1] if i + 1 < len(moves) else ()
        nxt = min(moves[i + 1][2]) if i + 1 < len(moves) else None
        rows.append(dict(D=D, Tf=Tf, front=front, arr=arrivals, nxt=nxt, passed=(Tf < D and not arrivals), reentry=(Tf >= D and bool(arrivals))))
    conveyor = [r['nxt'] == r['front'] for r in rows[:-1]]
    setters = Counter(min(st) for t, way, st, nx in moves)
    top_setter, top_n = setters.most_common(1)[0]
    last = rows[-1]
    return dict(S=S, n_moves=len(moves), n_pass=ps['n_pass'],
                passed=sum(r['passed'] for r in rows), reentry=sum(r['reentry'] for r in rows),
                conveyor_yes=sum(conveyor), conveyor_no=len(conveyor) - sum(conveyor),
                no_cases=[(S, i, rows[i]['front'], rows[i]['nxt'], rows[i]['arr']) for i, c in enumerate(conveyor) if not c][:2],
                top_setter_rank=rank[top_setter], top_n=top_n, n_distinct_setters=len(setters),
                land_front_rank=rank[last['front']], land_margin=last['Tf'] / last['D'] if last['D'] else None)


def chunk(first):
    return [r for r in (study((first,) + rest) for rest in itertools.combinations(range(first + 1, 25), 6)) if r]


def report(name, rows, w):
    rows = [r for r in rows if r]
    w("\n== %s: %d relays ==" % (name, len(rows)))
    w("  edge cases of the forced rule: the front reached the edge within the move but was out again at its end (passed through): %d moves;"
      " a reading carried in although the front had not reached the edge (a reading already in the slot at the move's start, re-entering): %d moves"
      % (sum(r['passed'] for r in rows), sum(r['reentry'] for r in rows)))
    y = sum(r['conveyor_yes'] for r in rows); n = sum(r['conveyor_no'] for r in rows)
    w("  C1 the next setter is the previous move's queue front: %d moves; not: %d moves" % (y, n))
    w("  C1 relays in which every hand-over is the queue front: %d of %d" % (sum(1 for r in rows if r['conveyor_no'] == 0), len(rows)))
    w("  C2 the reading setting the most moves, by rank (0 = slowest): %s" % dict(sorted(Counter(r['top_setter_rank'] for r in rows).items())))
    w("  C2 distinct setters per relay: %s" % dict(sorted(Counter(r['n_distinct_setters'] for r in rows).items())))
    w("  C3 at the landing, the queue front's rank: %s" % dict(sorted(Counter(r['land_front_rank'] for r in rows).items())))
    ms = sorted(r['land_margin'] for r in rows if r['land_margin'] is not None)
    if ms:
        w("  C3 margin T_front/D at the landing: least %s, lower quartile %s, median %s" %
          (float(ms[0]), float(ms[len(ms) // 4]), float(ms[len(ms) // 2])))
    ex = [c for r in rows for c in r['no_cases']][:12]
    w("  C1 examples where the next setter is not the front (set, move, front, next setter, carried in): %s" % ex)


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('e204_queue_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
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
        report('every relay to 24 with at least three passages', [r for part in pool.map(chunk, range(1, 19)) for r in part], w)
        report('late fine band shapes', pool.map(study, late_shapes()), w)
        report('Case C chains with at least two passages, readings <= 200', [study(S, 2) for S in cc1], w)
        report('Case C chains with at least two passages, readings <= 5,000', [study(S, 2) for S in cc2], w)
    out.close()
    print(open('e204_queue_v1.out').read()[len(__doc__):])
