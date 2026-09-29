"""E170 (2026-09-29): test candidate decreasing quantities on the cascade BEFORE formalising any termination theorem.

Owner: "do the tests for quantity before formalising".  Nothing here is formalised.

THE CHECK, fixed before any data was seen
-----------------------------------------
Object: the cascade of `LRC/Cascade/Iteration.lean` on whole-number readings S (at most seven), threshold 1/8, from the
bound t0 = 1/(8m), m = min S:  move(t) = t if lonely, else max over readings in the way (circDist(d t) < 1/8, strict) of
nextOpening(d, t) = (ceil(d t - 1/8) + 1/8)/d.  Exact rational arithmetic throughout.  States j = 0..N; t_N is the fixed
point (lonely).  Every quantity is computed from the state alone (no knowledge of N).

A quantity SURVIVES only if all four hold, on every chain of every population:
  (i)   strictly monotone along the chain (in one declared direction);
  (ii)  well-founded: integer-valued, or a real with a recorded positive minimum step;
  (iii) scale-free: the same sequence on S and on 3S (the AP is scale invariant; a rank that grows with scale is not
        a proof ingredient, E164-E166);
  (iv)  joint: not a function of one pair's state alone (for whole-number readings every pair's capture state recurs
        with period 1/gcd, HandoffDriftN.zero_drift_iff with (r, s) = (a/g, b/g)).
Violations are counted and the first ones listed individually.  A clean result is reported as clean.

Candidates (all at state j with readings in the way B_j non-empty):
  Q1 blocked      |B_j|                                                  integer
  Q2 lapgroups    number of distinct lap labels round(d t) over B_j      integer
  Q3 setterrank   rank in sorted S of the reading whose opening is t_{j+1} (smallest rank on ties)   integer
  Q4 setterlap    that reading's opening lap K (t_{j+1} = (K + 1/8)/setter)                          integer
  Q6 wait         8m (t_{j+1} - t_j)                                     real
  Q7 depth        sum over B_j of (1/8 - circDist(d t_j))                real
  Q8 horizon      8m * min over clear readings c of (deadline(c, t_j) - t_j), deadline = (lap + 7/8)/c   real
  Q9 deficit      MixedLapOverlapN budget: D = max B_j, P = t_j + 3/(4D); clear readings with c*3/(4D) <= slack are
                  protected (protected_clear_until); W = 0, 1/(4e), 1/(4a)+1/(2b) for 0, 1, 2 unprotected; undefined
                  for >= 3.  Delta = 8m (t_{j+1} + W - P).  Delta <= 0 is the Lean criterion certifying t_N <= P.
  Q11 control     openings of all readings remaining in (t_j, t_0 + 1).  Strictly decreasing BY CONSTRUCTION; must
                  FAIL (iii).  It is the positive control for the monotonicity count and the negative control for the
                  scale test.
Pair state (iv): at each hand-off, (a/m, b/m, depth8(a, b, K, L)) with a = setter at j, b = setter at j+1, K = a's
  opening lap, L = b's lap label at t_{j+1} (HandoffDriftN.depth8).  Counted: repeats of the same state within one chain.
Landing: single point iff some reading has d t_N = 7/8 mod 1 exactly (the setter sits at 1/8, so the left side is
  already closed).

Named test cases (from the review exchange, 2026-09-29):
  TC1 the AP 1..7; TC2 (99, 200, ..., 700), the whole-number form of (0.99, 2, ..., 7); TC3 chains containing a
  hand-off between readings in ratio 7:8; TC4 the late band shapes (coverB_fine_v1.late_shapes, fine scale 27720);
  TC5 E114's family (1, 5k-2, 5k, 10k-2), cascade length 2k+1.
Populations: Case B to 24 exhaustive (7-subsets of [1, 24] with 7 min < max), Case C sample (20,000 random 7-subsets
  of [1, 200] with max > 24 min, seed 5), late band shapes.
Consistency checks against the Lean: t_N <= P_j whenever Delta_j <= 0 (MixedLapOverlapN.protected_group_overlaps_*,
  with iterate_le_of_lonely); iterates strictly increase; every chain ends before t_0 + 1.
"""
import sys, math, random, itertools, json
from fractions import Fraction as F
from collections import Counter, defaultdict
from multiprocessing import Pool

E8 = F(1, 8)
QS = ['Q1_blocked', 'Q2_lapgroups', 'Q3_setterrank', 'Q4_setterlap', 'Q6_wait', 'Q7_depth', 'Q8_horizon',
      'Q9_deficit', 'Q11_control']
INTEGER = {'Q1_blocked', 'Q2_lapgroups', 'Q3_setterrank', 'Q4_setterlap', 'Q11_control'}


def cd(x):
    f = x - math.floor(x)
    return min(f, 1 - f)


def next_opening(d, t):
    return (math.ceil(d * t - E8) + E8) / d


def cascade(S, cap=100000):
    S = sorted(S); m = S[0]; t0 = F(1, 8 * m); t = t0; states = []
    while True:
        B = [d for d in S if cd(d * t) < E8]
        if not B:
            states.append((t, B, None)); return states, True
        nxt = max(next_opening(d, t) for d in B)
        assert nxt > t
        setters = [d for d in B if next_opening(d, t) == nxt]
        states.append((t, B, setters))
        t = nxt
        if t > t0 + 1 or len(states) > cap:
            return states, False


def openings_left(S, t, tend):
    # openings (k + 1/8)/d strictly inside (t, tend)
    tot = 0
    for d in S:
        a = d * t - E8; b = d * tend - E8
        tot += max(0, math.ceil(b) - math.floor(a) - 1)
    return tot


def quantities(S):
    S = sorted(S); m = S[0]; rank = {d: i for i, d in enumerate(S)}
    states, ended = cascade(S)
    N = len(states) - 1; t0 = states[0][0]; tN = states[-1][0]
    rows = []
    for j in range(N):
        t, B, setters = states[j]; tn = states[j + 1][0]
        s = min(setters, key=lambda d: rank[d]); K = math.ceil(s * t - E8)
        clear = [c for c in S if c not in B]
        q = {}
        q['Q1_blocked'] = len(B)
        q['Q2_lapgroups'] = len({math.floor(d * t + F(1, 2)) for d in B})
        q['Q3_setterrank'] = rank[s]
        q['Q4_setterlap'] = K
        q['Q6_wait'] = 8 * m * (tn - t)
        q['Q7_depth'] = sum(E8 - cd(d * t) for d in B)
        q['Q8_horizon'] = (8 * m * min((math.floor(c * t - E8) + F(7, 8)) / c - t for c in clear)) if clear else None
        D = max(B); P = t + F(3, 4) / D
        unprot = sorted(c for c in clear if c * F(3, 4) / D > math.floor(c * t - E8) + F(7, 8) - c * t)
        if len(unprot) == 0: W = F(0)
        elif len(unprot) == 1: W = F(1, 4 * unprot[0])
        elif len(unprot) == 2: W = F(1, 4 * unprot[0]) + F(1, 2 * unprot[1])
        else: W = None
        q['Q9_deficit'] = None if W is None else 8 * m * (tn + W - P)
        q['_certified'] = (W is not None and tn + W <= P)
        q['_P'] = P
        q['Q11_control'] = openings_left(S, t, t0 + 1)
        q['_setter'] = s; q['_K'] = K; q['_t'] = t
        rows.append(q)
    # pair states at hand-offs j -> j+1 (both setters defined)
    pairs = []
    for j in range(N - 1):
        a = rows[j]['_setter']; K = rows[j]['_K']; b = rows[j + 1]['_setter']; tn = states[j + 1][0]
        L = math.floor(b * tn + F(1, 2))
        depth = 8 * L + 1 - (8 * K + 1) * F(b, a)
        pairs.append((F(a, m), F(b, m), depth))
    fr = tN * 1 - math.floor(tN)  # unused
    single = any((d * tN - math.floor(d * tN)) == F(7, 8) for d in S)
    return dict(S=tuple(S), N=N, ended=ended, R=8 * m * tN, rows=rows, pairs=pairs, single=single, tN=tN)


def tally(res):
    """Per-quantity transition counts and chain-level monotonicity (chains with >= 2 moves); violations listed."""
    out = {}
    for Q in QS:
        tr = Counter(); chains = Counter(); minstep = None; ex = defaultdict(list)
        for r in res:
            if r['N'] < 2:
                continue
            vals = [row[Q] for row in r['rows']]
            chains['chains>=2moves'] += 1
            if any(v is None for v in vals):
                chains['undefined_somewhere'] += 1
            pairs = [(x, y) for x, y in zip(vals, vals[1:]) if x is not None and y is not None]
            for x, y in pairs:
                if y < x:
                    tr['dec'] += 1
                    if minstep is None or x - y < minstep: minstep = x - y
                elif y == x:
                    tr['eq'] += 1
                    if len(ex['eq']) < 2: ex['eq'].append((r['S'], [str(v) for v in vals]))
                else:
                    tr['inc'] += 1
                    if len(ex['inc']) < 2: ex['inc'].append((r['S'], [str(v) for v in vals]))
            full = len(pairs) == len(vals) - 1
            if full and all(y < x for x, y in pairs): chains['strictly_dec'] += 1
            if full and all(y <= x for x, y in pairs): chains['nonincreasing'] += 1
            if full and all(y > x for x, y in pairs): chains['strictly_inc'] += 1
        out[Q] = dict(transitions=dict(tr), chains=dict(chains), min_dec_step=str(minstep), examples=dict(ex))
    return out


def lean_consistency(res):
    bad = []
    for r in res:
        if not r['ended']:
            bad.append(('did not end within one period', r['S'])); continue
        for row in r['rows']:
            if row['_certified'] and not (r['tN'] <= row['_P']):
                bad.append(('certified but t_N > P', r['S']))
    return bad


def pair_repeats(res):
    c = Counter(); ex = []
    for r in res:
        cnt = Counter(r['pairs'])
        rep = sum(v - 1 for v in cnt.values() if v > 1)
        if rep:
            c['chains_with_repeat'] += 1; c['repeats'] += rep
            if len(ex) < 3: ex.append((r['S'], [(str(a), str(b), str(d)) for (a, b, d), v in cnt.items() if v > 1][:2]))
        c['chains_with_handoff'] += bool(r['pairs'])
    return dict(c), ex


def scale_test(sets):
    diff = Counter(); n = 0
    for S in sets:
        a = quantities(S); b = quantities([3 * d for d in S]); n += 1
        for Q in QS:
            va = [row[Q] for row in a['rows']]; vb = [row[Q] for row in b['rows']]
            if va != vb: diff[Q] += 1
        if a['N'] != b['N']: diff['N'] += 1
    return n, dict(diff)


def summary(res):
    Ns = Counter(r['N'] for r in res)
    return dict(sets=len(res), maxN=max(Ns), N_dist=dict(sorted(Ns.items())[:12]),
                maxR=str(max(r['R'] for r in res)), maxR_float=float(max(r['R'] for r in res)),
                single_point_landings=sum(r['single'] for r in res),
                ratio78_handoffs=sum(any({a / b, b / a} & {F(7, 8), F(8, 7)} for a, b, _ in r['pairs']) for r in res))


def work(sets):
    return [quantities(S) for S in sets]


def strip(r):
    r = dict(r); r['rows'] = [{k: v for k, v in row.items()} for row in r['rows']]; return r


def run_pop(name, sets, pool, log):
    chunks = [sets[i::32] for i in range(32)]
    res = [r for part in pool.map(work, chunks) for r in part]
    log.write("\n== %s ==\n" % name)
    log.write("summary: %s\n" % summary(res))
    bad = lean_consistency(res)
    log.write("Lean consistency (certified => t_N <= P; ended within a period): %d violations %s\n" % (len(bad), bad[:3]))
    pr, pex = pair_repeats(res)
    log.write("pair-state repeats within a chain: %s  first: %s\n" % (pr, pex))
    T = tally(res)
    for Q in QS:
        log.write("  %-14s %s\n" % (Q, {k: T[Q][k] for k in ('transitions', 'chains', 'min_dec_step')}))
        for kind, lst in T[Q]['examples'].items():
            for S, vals in lst[:2]:
                log.write("        %s e.g. %s : %s\n" % (kind, S, vals[:10]))
    log.flush()
    return res


def trace(S, log, label):
    r = quantities(S)
    log.write("\n-- trace %s  S=%s  moves N=%d  R*=%s (%.4f)  single-point landing=%s\n" %
              (label, r['S'], r['N'], r['R'], float(r['R']), r['single']))
    for j, row in enumerate(r['rows']):
        log.write("   j=%d t=%s " % (j, row['_t']) + " ".join("%s=%s" % (Q.split('_')[0], row[Q] if row[Q] is None or Q in INTEGER else round(float(row[Q]), 4)) for Q in QS) + " cert=%s\n" % row['_certified'])
    log.write("   pair states: %s\n" % [(str(a), str(b), str(d)) for a, b, d in r['pairs']])


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    out = open('quantity_tests_v1.out', 'w')
    out.write(__doc__ + "\n")
    # named cases
    trace([1, 2, 3, 4, 5, 6, 7], out, 'TC1 AP 1..7')
    trace([99, 200, 300, 400, 500, 600, 700], out, 'TC2 (99,200..700)')
    for k in range(2, 11):
        r = quantities([1, 5 * k - 2, 5 * k, 10 * k - 2])
        out.write("TC5 k=%d S=%s moves N=%d (E114 says 2k+1 = %d)\n" % (k, r['S'], r['N'], 2 * k + 1))
    out.flush()
    with Pool(8) as pool:
        caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]]
        resB = run_pop('Case B to 24 (exhaustive)', caseB, pool, out)
        rng = random.Random(5); caseC = []
        while len(caseC) < 20000:
            T = tuple(sorted(rng.sample(range(1, 201), 7)))
            if T[-1] > 24 * T[0]: caseC.append(T)
        resC = run_pop('Case C sample (20,000, readings <= 200)', caseC, pool, out)
        from coverB_fine_v1 import late_shapes
        late = late_shapes()
        resL = run_pop('late band shapes (TC4)', late, pool, out)
    # TC3: chains with a 7:8 hand-off, one traced
    for res in (resB, resC, resL):
        for r in res:
            if any({a / b, b / a} & {F(7, 8), F(8, 7)} for a, b, _ in r['pairs']):
                trace(list(r['S']), out, 'TC3 (a 7:8 hand-off)'); break
    # the longest chains, traced
    for name, res in (('Case B', resB), ('Case C', resC), ('late', resL)):
        r = max(res, key=lambda r: r['N']); trace(list(r['S']), out, 'longest chain, %s' % name)
    # scale test
    samp = [r['S'] for r in resB if r['N'] >= 2][::50] + [r['S'] for r in resL][::20]
    n, diff = scale_test(samp)
    out.write("\n== scale test (S vs 3S) on %d sets with >= 2 moves: sequences differing per quantity %s\n" % (n, diff))
    out.close()
    print(open('quantity_tests_v1.out').read()[-6000:])
