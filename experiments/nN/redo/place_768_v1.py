"""E175 (2026-09-29): the 768 incidents E174 left unplaced, run through the cascade.

Owner: "yes place the 768 through the cascade and see what is happen there".

For each of the 768 (sets of seven readings in 1..24 whose incident is not a named view, not one separation from one,
and not the stretch at a rung a/q with q <= 8):
  * the cascade's trace from the bound: each move, the readings in the subject's slot, the runner that leaves;
  * the incident: host (reading at its opening), lap, closer (first reading to close after), stretch width;
  * rungs a/q with q up to 40 (the menu stopped at 8): the least q for which the incident is
        Q0  the rung itself (t* = a/q),
        Q1  the rung displaced by one separation (the rung is not lonely and t* = move(a/q)),
        Q2  the stretch at the rung (t* = the latest opening at or before a/q);
    and, for that rung, which readings are in the way there and how q relates to them (q divides a reading, q is a
    reading, neither);
  * one reading at a time moved by +-1 through the cascade: where the isolation lands (E174's places S0, S1, S2, or
    unplaced again), and which ranks' moves place it.
"""
import math
from fractions import Fraction as F
from collections import Counter, defaultdict
from multiprocessing import Pool
from math import gcd
from place_incidents_v1 import cascade, move, lonely, boundaries, place
from place_incidents_v1b import misses_of, last_opening
from quantity_tests_v1 import cd, E8

QMAX = 40


def trace(T):
    t = F(1, 8 * T[0]); out = []
    while True:
        nx, setters = move(T, t)
        way = [d for d in T if cd(d * t) < E8]
        out.append((t, way, setters))
        if setters is None:
            return out
        t = nx


def place_full(T):
    ts, n = cascade(T)
    p = place(T, ts)
    if p[0] != 'miss':
        return p[0], p[1]
    for q in range(2, 9):
        for a in range(1, q):
            if gcd(a, q) == 1 and F(a, q) >= ts and max(last_opening(e, F(a, q)) for e in T) == ts:
                return 'S2', F(a, q)
    return 'unplaced', None


def rung_places(T, ts):
    """Least q (2..QMAX) giving Q0, Q1 or Q2, with the rung."""
    found = {}
    for q in range(2, QMAX + 1):
        for a in range(1, q):
            if gcd(a, q) != 1:
                continue
            r = F(a, q)
            if r > 4 * ts:
                break
            if 'Q0' not in found and r == ts:
                found['Q0'] = r
            if 'Q1' not in found and r < ts and not lonely(T, r) and move(T, r)[0] == ts:
                found['Q1'] = r
            if 'Q2' not in found and r >= ts and max(last_opening(e, r) for e in T) == ts:
                found['Q2'] = r
    return found


def relate(T, r):
    q = r.denominator
    way = [d for d in T if cd(d * r) < E8]
    return dict(q=q, way=way, q_divides=[d for d in T if d % q == 0], q_is_reading=q in T,
                way_multiple_of_q=[d for d in way if d % q == 0])


def perturb(T):
    res = []
    for i in range(7):
        for dlt in (-1, 1):
            U = list(T); U[i] += dlt
            if U[i] < 1 or len(set(U)) < 7:
                continue
            U = tuple(sorted(U))
            ts, n = cascade(U)
            kind, where = place_full(U)
            res.append((i, dlt, U, 8 * U[0] * ts, kind, where))
    return res


def analyse(T):
    T = tuple(T)
    tr = trace(T); ts = tr[-1][0]
    b = boundaries(T, ts)
    rp = rung_places(T, ts)
    rel = {k: relate(T, r) for k, r in rp.items()}
    return dict(T=T, ts=ts, R=8 * T[0] * ts, moves=len(tr) - 1, trace=tr, b=b, rp=rp, rel=rel, pert=perturb(T))


def unplaced_of(first):
    return [x['T'] for x in misses_of(first) if x['s2'] is None]


if __name__ == '__main__':
    with Pool(8) as pool:
        sets = [T for part in pool.map(unplaced_of, range(1, 19)) for T in part]
        res = pool.map(analyse, sets)
    out = open('place_768_v1.out', 'w'); out.write(__doc__ + "\n")
    out.write("sets: %d\n" % len(res))
    out.write("moves from the bound: %s\n" % dict(sorted(Counter(x['moves'] for x in res).items())))
    out.write("incident: host rank %s; closer rank %s; single point %d\n" %
              (dict(sorted(Counter(x['b']['host'] for x in res).items(), key=str)),
               dict(sorted(Counter(x['b']['closer'] for x in res).items())), sum(x['b']['tight'] for x in res)))
    # rungs beyond q = 8
    for k in ('Q0', 'Q1', 'Q2'):
        has = [x for x in res if k in x['rp']]
        out.write("%s: %d sets; least q %s\n" % (k, len(has), dict(sorted(Counter(x['rp'][k].denominator for x in has).items()))))
    anyq = [x for x in res if x['rp']]
    best = [min(x['rp'].values(), key=lambda r: r.denominator) for x in anyq]
    out.write("placed by some rung with q <= %d: %d of %d; by least q: %s\n" %
              (QMAX, len(anyq), len(res), dict(sorted(Counter(r.denominator for r in best).items()))))
    q1 = [x for x in res if 'Q1' in x['rp']]
    out.write("Q1 rungs: %s\n" % dict(Counter(str(x['rp']['Q1']) for x in q1).most_common(15)))
    out.write("Q1: runner that leaves = the only reading in the way at the rung: %d of %d\n" %
              (sum(len(x['rel']['Q1']['way']) == 1 for x in q1), len(q1)))
    out.write("Q1: q divides some reading %d; q is a reading %d; a reading in the way is a multiple of q %d (of %d)\n" %
              (sum(bool(x['rel']['Q1']['q_divides']) for x in q1), sum(x['rel']['Q1']['q_is_reading'] for x in q1),
               sum(bool(x['rel']['Q1']['way_multiple_of_q']) for x in q1), len(q1)))
    none = [x for x in res if not x['rp']]
    out.write("not placed by any rung q <= %d: %d\n" % (QMAX, len(none)))
    # perturbation
    dest = Counter(); ranks = Counter(); per = Counter()
    for x in res:
        placed_ranks = set()
        for i, dlt, U, R, kind, where in x['pert']:
            dest[(kind, str(where) if kind == 'S2' else where)] += 1
            if kind != 'unplaced':
                placed_ranks.add(i)
        per[len(placed_ranks)] += 1
        for i in placed_ranks:
            ranks[i] += 1
    out.write("\nperturbation (one reading +-1): destinations %s\n" % dict(dest.most_common(20)))
    out.write("ranks whose move places the isolation (sets counted per rank): %s\n" % dict(sorted(ranks.items())))
    out.write("number of ranks whose move places it, per set: %s\n" % dict(sorted(per.items())))
    # traces
    out.write("\ntraces (first 16): readings; moves t (R), readings in the slot, runner(s) leaving; incident; rungs\n")
    for x in res[:16]:
        T = x['T']; m = T[0]
        out.write("\n%s  lands t*=%s R=%s  host %s/K%s closer %s/L%s\n" %
                  (T, x['ts'], x['R'], T[x['b']['host']], x['b']['K'], T[x['b']['closer']], x['b']['L']))
        for t, way, setters in x['trace']:
            out.write("   t=%s R=%.4f  in slot %s  leaves %s\n" % (t, float(8 * m * t), way, setters))
        for k, r in x['rp'].items():
            out.write("   %s at rung %s: in the way there %s; readings divisible by %d: %s\n" %
                      (k, r, x['rel'][k]['way'], r.denominator, x['rel'][k]['q_divides']))
        pl = [(i, dlt, float(R), kind, str(where)) for i, dlt, U, R, kind, where in x['pert'] if kind != 'unplaced']
        out.write("   perturbations that place it: %s\n" % [(T[i], dlt, round(R, 3), kind, w) for i, dlt, R, kind, w in pl])
    out.write("\nnot placed by any rung (first 20): %s\n" % [(x['T'], x['R']) for x in none[:20]])
    out.close()
    print(open('place_768_v1.out').read()[len(__doc__):])
