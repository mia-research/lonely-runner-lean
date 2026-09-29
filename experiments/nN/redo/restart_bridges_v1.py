"""E183 (2026-09-29): how much of the restarted cascade after a death the pairwise separation bounds control.

Owner: "yes try making the pairwise separation bound control the restart".

After a death (E182, case 3) the new landing is the cascade restarted at the dying instant: first the entering runner
b's exit, then further moves.  Each move's setter relative to the previous one (SweepBridgeN): SWEEP (slower, same lap),
BRIDGE DOWN (slower, earlier lap), BRIDGE UP (faster, later lap).  Derived: between bridges up the setter's rank
strictly falls, so a run has at most 7 moves and the restart has at most 7 (U + 1) moves, U = bridges up.
Recorded exactly for every case-3 restart of E182's populations:
  * U, the moves, and the check moves <= 7 (U + 1) (derived; must hold);
  * every sweep step against the proved pair bound k < (s_a + s_b)/(8 (s_a - s_b)) (sweep_lap_bound; must hold);
  * every bridge up: the pair (setter a -> faster b), whether the same pair bridges up again in the same restart
    (then HandoffDriftN's drift bound applies), and the residue (8k+1) b mod 8a that let b into the slot.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from quantity_tests_v1 import cd, E8, next_opening

DELTA = F(1, 10 ** 15)
_orig = D.classify


def classify_k(x, sa, ka, sb, kb):
    rec = _orig(x, sa, ka, sb, kb)
    rec['ka'], rec['kb'] = ka, kb
    return rec


D.classify = classify_k


def restart_moves(ds, t_start, first_setter, first_lap):
    """Moves of the cascade from t_start, where first_setter has just exited lap first_lap (t_start is its opening)."""
    moves = []                       # (setter index, its lap K at the exit it sets)
    prev, prevK = first_setter, first_lap
    t = t_start
    for _ in range(1000):
        way = [i for i, d in enumerate(ds) if cd(d * t) < E8]
        if not way:
            return moves, t
        nx = max(next_opening(ds[i], t) for i in way)
        setter = min(i for i in way if next_opening(ds[i], t) == nx)
        K = math.ceil(ds[setter] * t - E8)          # the setter's opening lap: nx = (K + 1/8)/d
        L = math.floor(ds[setter] * t + F(1, 2))
        if ds[setter] > ds[prev]:
            typ = 'up'
        else:
            typ = 'sweep' if L == prevK else 'down'
        moves.append(dict(setter=setter, prev=prev, prevK=prevK, L=L, typ=typ,
                          ok_sweep=(typ != 'sweep' or 8 * prevK * (ds[prev] - ds[setter]) < ds[prev] + ds[setter]),
                          residue=((8 * prevK + 1) * ds[setter] / ds[prev]) % 8 if typ == 'up' else None))
        prev, prevK = setter, K
        t = nx
    return moves, None


def study(S):
    S = tuple(sorted(S)); x = [F(7 * d, S[-1]) for d in S]
    r = D.follow(S)
    rows = []
    for e in r['events']:
        if e.get('kind') != 'death' or e.get('tau') is None or e['tau'] == 0 or not e['simple']:
            continue
        tau, t0, k = e['tau'], e['t0'], e['ka']
        d0 = D.readings_at(x, tau)
        pos = [d * t0 - math.floor(d * t0) for d in d0]
        a = pos.index(E8); b = pos.index(F(7, 8))
        ds = D.readings_at(x, tau + DELTA)
        Tb = F(8 * (k[b] + 1) + 1, 8) / ds[b]
        if cd(ds[b] * Tb) != E8:
            continue
        land = D.components(ds, need=1)[0][0]
        if land <= Tb:
            continue                                   # cases 1 and 2
        moves, end = restart_moves(ds, Tb, b, k[b] + 1)
        U = sum(1 for mv in moves if mv['typ'] == 'up')
        pairs = Counter((mv['prev'], mv['setter']) for mv in moves if mv['typ'] == 'up')
        rows.append(dict(n=len(moves), U=U, ok_struct=(len(moves) + 1 <= 7 * (U + 1)), end_ok=(end == land),
                         sweeps_ok=all(mv['ok_sweep'] for mv in moves), repeat=any(v > 1 for v in pairs.values()),
                         types=tuple(mv['typ'] for mv in moves)))
    return rows


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::100]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    out = open('restart_bridges_v1.out', 'w'); out.write(__doc__ + "\n")
    with Pool(8) as pool:
        for name, sets in [('Case B to 24, every 100th', caseB), ('late band shapes, every 10th', late_shapes()[::10]),
                           ('Case C sample (500)', caseC)]:
            rows = [x for rs in pool.map(study, sets) for x in rs]
            out.write("\n== %s: case-3 restarts %d ==\n" % (name, len(rows)))
            out.write("  restart reaches the landing: %d; moves <= 7 (U+1) (derived): %d; every sweep within the pair bound: %d\n" %
                      (sum(x['end_ok'] for x in rows), sum(x['ok_struct'] for x in rows), sum(x['sweeps_ok'] for x in rows)))
            out.write("  bridges up per restart U: %s\n" % dict(sorted(Counter(x['U'] for x in rows).items())))
            out.write("  restarts with no bridge up (pairwise-controlled, at most 6 further moves): %d of %d\n" %
                      (sum(1 for x in rows if x['U'] == 0), len(rows)))
            out.write("  restarts where the same pair bridges up twice (drift bound applies): %d\n" % sum(x['repeat'] for x in rows))
            out.write("  move-type patterns (top 10): %s\n" % Counter(x['types'] for x in rows).most_common(10))
    out.close()
    print(open('restart_bridges_v1.out').read()[len(__doc__):])
