"""E171 (2026-09-29): the oracle's isolation incidents, and monotonicity by waves.  Checks fixed before any data.

Owner: "run the wave-level test.  Make sure it is backed up by cascade and [check you are not] trying to find a density
or something else creeping."  Then: "Think about what we are trying to prove not what others have tried.  It is about
boundaries, isolation incidents that we have an oracle for that works exactly and perfectly."

THE ORACLE.  The cascade of LRC/Cascade/Iteration.lean: move(t) = t if lonely, else the max over readings in the way
(circDist(d t) < 1/8, strict) of nextOpening(d, t) = (ceil(d t - 1/8) + 1/8)/d, from t0 = 1/(8m); exact rationals.
It lands on the FIRST isolation incident t* >= t0 (first_isolation_of_fixed; lonely_iff_run_ends).

CASCADE CHECKS (must be 0 violations before any result is read):
  C1 the landing equals the first lonely instant >= t0 computed WITHOUT the cascade (intersection of every reading's
     closed clear intervals [(k+1/8)/d, (k+7/8)/d], linear merge, window [t0, t* + 2/m]);
  C2 every move type agrees with SweepBridgeN: a faster next setter is on a later lap, a slower one on the same or an
     earlier lap.

NO DENSITY CREEP.  Everything below is read at a cascade state or at an incident: which reading opens (sits exactly at
k + 1/8), which closes first, the lap assignment k_d = floor(d t*), the readings in the subject's slot, the setter and
its lap, the clear readings' deadlines (LapDeadlineN).  No measure, density, proportion of time or count over an interval.

PART A, INCIDENTS (the boundary structure of what we are proving exists).  At t*:
  openers  readings with d t* = k + 1/8 exactly (never empty: the last setter, or the nearest runner at the bound);
  closer   the reading whose clear band [k+1/8, k+7/8] ends first after t*; width w = that end - t*; TIGHT iff w = 0
           (a single-point incident: an opening and a closing boundary meet);
  lap assignment k_d = floor(d t*) (the incident is exactly this assignment passing the pairwise test,
           TwoBlock.lonely_eight_of_pairwise_laps; max lower end = opener, min upper end = closer).
  GRID DESCRIPTION: is k the lap assignment of a grid-class instant of the arrangement's own grid, RegimeSkeletonN
  GridClass8 S e mm c with e in S, 1 <= mm <= 4, c in {1,3,5,7}: for every d some n >= 1 with |n e - mm d| < e and
  k_d = floor(c n/8) (or one less when c n = 0 mod 8).  Reported: coverage, least mm, the (rank e, mm, c) catalogue.
  CONTROL (tautology check, E129's lesson): the same test on the SECOND incident (left end of the next lonely component
  after the first, computed by the independent intersection), compared bin by bin in R = 8 m t (bins [1,2), [2,4),
  [4,8), [8,16), [16,32)).  If the second incidents are covered at the same rate in the same R bin, the description is
  generic for lonely instants there and says nothing special about the oracle's incident.

PART B, WAVES (E170 follow-up).  Cut each chain at every bridge up (next setter faster); within a wave the setter's rank
strictly descends, so a wave has at most seven moves.  Candidates at each wave start: V2 readings in the way; V3 start
rank; V4 end rank; V5 wave length; V7 opening setter's own lap; V10 horizon of the clear readings (8m units); V11 lap
jump of the bridge opening the wave; V14 R (a control, increasing by construction).  Survival: strictly monotone across
the waves of every chain with >= 2 waves, well-founded, scale-free (S vs 3S), joint.  Also: waves per chain.

Populations: Case B to 24 (exhaustive), Case C sample (20,000, readings <= 200, seed 5), late band shapes.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter, defaultdict
from multiprocessing import Pool
from quantity_tests_v1 import cascade, cd, E8

UNITS = (1, 3, 5, 7)
BINS = [(1, 2), (2, 4), (4, 8), (8, 16), (16, 32)]
VS = ['V2_blocked', 'V3_startrank', 'V4_endrank', 'V5_length', 'V7_firstlap', 'V10_horizon', 'V11_lapjump',
      'V14_R_control']


def lonely_components(S, lo, hi):
    """Closed lonely components within [lo, hi], by linear-merge intersection of clear intervals.  No cascade."""
    cur = [(lo, hi)]
    for d in S:
        blocks = [(max(lo, F(8 * k + 1, 8 * d)), min(hi, F(8 * k + 7, 8 * d)))
                  for k in range(max(0, math.floor(d * lo) - 1), math.floor(d * hi) + 2)]
        blocks = [b for b in blocks if b[0] <= b[1]]
        nxt = []; i = j = 0
        while i < len(cur) and j < len(blocks):
            x = max(cur[i][0], blocks[j][0]); y = min(cur[i][1], blocks[j][1])
            if x <= y:
                nxt.append((x, y))
            if cur[i][1] < blocks[j][1]:
                i += 1
            else:
                j += 1
        cur = nxt
        if not cur:
            break
    return cur


def allowed_laps(d, e, mm, c):
    L = set(); x = F(mm * d, e)
    for n in range(max(1, math.floor(x) - 1), math.ceil(x) + 2):
        if abs(n * e - mm * d) < e:
            L.add((c * n) // 8)
            if (c * n) % 8 == 0:
                L.add((c * n) // 8 - 1)
    return L


def grid_descriptions(S, t, rank):
    k = {d: math.floor(d * t) for d in S}
    out = []
    for e in S:
        for mm in range(1, 5):
            for c in UNITS:
                if all(k[d] in allowed_laps(d, e, mm, c) for d in S):
                    out.append((rank[e], mm, c))
    return out


def incident(S, t, rank, m):
    openers = [d for d in S if d * t - math.floor(d * t) == E8]
    ends = {d: (math.floor(d * t) + F(7, 8)) / d for d in S}
    wmin = min(ends.values()) - t
    closers = [d for d in S if ends[d] - t == wmin]
    desc = grid_descriptions(S, t, rank)
    return dict(R=8 * m * t, opener=min(rank[d] for d in openers) if openers else None,
                closer=min(rank[d] for d in closers), tight=(wmin == 0), width=8 * m * wmin, desc=desc)


def rbin(R):
    for a, b in BINS:
        if a <= R < b:
            return (a, b)
    return None


def analyse(S):
    S = sorted(S); m = S[0]; rank = {d: i for i, d in enumerate(S)}
    states, ended = cascade(S)
    N = len(states) - 1
    t0, tN = states[0][0], states[-1][0]
    comps = lonely_components(S, t0, tN + F(2, m))
    c1 = ended and bool(comps) and comps[0][0] == tN
    first = incident(S, tN, rank, m)
    second = incident(S, comps[1][0], rank, m) if len(comps) > 1 else None
    # waves
    setters = [min(st[2], key=lambda d: rank[d]) for st in states[:N]]
    Ks = [math.ceil(setters[j] * states[j][0] - E8) for j in range(N)]
    types = []; c2 = True
    for j in range(N - 1):
        a, b = setters[j], setters[j + 1]; tn = states[j + 1][0]
        K = Ks[j]; L = math.floor(b * tn + F(1, 2))
        if b > a:
            types.append('up'); c2 = c2 and (L > K)
        else:
            types.append('sweep' if L == K else 'down'); c2 = c2 and (L <= K)
    starts = ([0] + [j + 1 for j, ty in enumerate(types) if ty == 'up']) if N > 0 else []
    waves = []
    for i, s0 in enumerate(starts):
        e0 = (starts[i + 1] - 1) if i + 1 < len(starts) else N - 1
        t, B, _ = states[s0]
        clear = [c for c in S if c not in B]
        w = {'V2_blocked': len(B), 'V3_startrank': rank[setters[s0]], 'V4_endrank': rank[setters[e0]],
             'V5_length': e0 - s0 + 1, 'V7_firstlap': Ks[s0],
             'V10_horizon': (8 * m * min((math.floor(c * t - E8) + F(7, 8)) / c - t for c in clear)) if clear else None,
             'V11_lapjump': (math.floor(setters[s0] * t + F(1, 2)) - Ks[s0 - 1]) if s0 > 0 else None,
             'V14_R_control': 8 * m * t}
        assert all(rank[setters[j + 1]] < rank[setters[j]] for j in range(s0, e0))
        waves.append(w)
    return dict(S=tuple(S), N=N, c1=c1, c2=c2, first=first, second=second, types=types, waves=waves)


def work(sets):
    return [analyse(S) for S in sets]


def report_incidents(name, res, out):
    out.write("\n== %s ==  sets %d\n" % (name, len(res)))
    out.write("cascade checks: C1 landing = independent first lonely instant: %d violations; C2 move types agree with "
              "SweepBridgeN: %d violations\n" % (sum(not r['c1'] for r in res), sum(not r['c2'] for r in res)))
    bad = [r['S'] for r in res if not (r['c1'] and r['c2'])][:3]
    if bad:
        out.write("   FIRST VIOLATIONS: %s\n" % bad)
    F1 = [r['first'] for r in res]
    out.write("PART A, first incidents: tight (single point) %d of %d; opener rank %s; closer rank %s\n" %
              (sum(i['tight'] for i in F1), len(F1), dict(sorted(Counter(i['opener'] for i in F1).items(), key=str)),
               dict(sorted(Counter(i['closer'] for i in F1).items()))))
    out.write("  (opener, closer, tight) types, top 12: %s\n" %
              Counter((i['opener'], i['closer'], i['tight']) for i in F1).most_common(12))
    cov = sum(bool(i['desc']) for i in F1)
    out.write("  grid description (e in S, mm <= 4, c unit): %d of %d first incidents covered\n" % (cov, len(F1)))
    lm = Counter(min(mm for _, mm, _ in i['desc']) if i['desc'] else None for i in F1)
    out.write("  least mm: %s\n" % dict(sorted(lm.items(), key=str)))
    cat = Counter(min(i['desc'], key=lambda x: (x[1], x[2], -x[0])) for i in F1 if i['desc'])
    out.write("  catalogue: %d distinct least descriptions (rank e, mm, c); top 12 %s\n" % (len(cat), cat.most_common(12)))
    unc = [(r['S'], float(r['first']['R']), r['first']['tight']) for r in res if not r['first']['desc']][:6]
    if unc:
        out.write("  uncovered first incidents (S, R, tight): %s\n" % unc)
    out.write("  CONTROL, matched by R bin -- coverage first vs second incident:\n")
    for bn in BINS:
        f = [r['first'] for r in res if rbin(r['first']['R']) == bn]
        s = [r['second'] for r in res if r['second'] is not None and rbin(r['second']['R']) == bn]
        if f or s:
            out.write("    R in [%d,%d): first %d/%d  second %d/%d\n" %
                      (bn[0], bn[1], sum(bool(i['desc']) for i in f), len(f), sum(bool(i['desc']) for i in s), len(s)))
    out.flush()


def report_waves(name, res, out):
    tc = Counter(ty for r in res for ty in r['types'])
    nw = Counter(len(r['waves']) for r in res if r['N'] > 0)
    out.write("PART B, waves: move types %s; waves per chain %s\n" % (dict(tc), dict(sorted(nw.items()))))
    multi = [r for r in res if len(r['waves']) >= 2]
    out.write("  chains with >= 2 waves: %d\n" % len(multi))
    for V in VS:
        tr = Counter(); ch = Counter(); ex = defaultdict(list)
        for r in multi:
            vals = [w[V] for w in r['waves']]
            if V == 'V11_lapjump':
                vals = vals[1:]
            if len(vals) < 2:
                continue
            prs = [(x, y) for x, y in zip(vals, vals[1:]) if x is not None and y is not None]
            full = len(prs) == len(vals) - 1
            for x, y in prs:
                k = 'dec' if y < x else ('eq' if y == x else 'inc'); tr[k] += 1
                if len(ex[k]) < 1:
                    ex[k].append((r['S'], [str(v) for v in vals][:8]))
            ch['chains'] += 1
            if full and all(y < x for x, y in prs): ch['strictly_dec'] += 1
            if full and all(y > x for x, y in prs): ch['strictly_inc'] += 1
        out.write("  %-15s transitions %s  chains %s\n" % (V, dict(tr), dict(ch)))
        for k in ('inc', 'dec', 'eq'):
            for S, vals in ex.get(k, []):
                out.write("        %s e.g. %s : %s\n" % (k, S, vals))
    out.flush()


def scale_test(sets):
    diff = Counter()
    for S in sets:
        a = analyse(S); b = analyse([3 * d for d in S])
        for V in VS:
            if [w[V] for w in a['waves']] != [w[V] for w in b['waves']]:
                diff[V] += 1
        if (a['first']['opener'], a['first']['closer'], a['first']['tight'], a['first']['desc']) != \
           (b['first']['opener'], b['first']['closer'], b['first']['tight'], b['first']['desc']):
            diff['incident'] += 1
    return len(sets), dict(diff)


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    out = open('wave_incident_v1.out', 'w'); out.write(__doc__ + "\n")
    from coverB_fine_v1 import late_shapes
    rng = random.Random(5); caseC = []
    while len(caseC) < 20000:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    pops = [('Case B to 24 (exhaustive)', [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]]),
            ('Case C sample (20,000, readings <= 200)', caseC), ('late band shapes', late_shapes())]
    allres = {}
    with Pool(8) as pool:
        for name, sets in pops:
            res = [r for part in pool.map(work, [sets[i::32] for i in range(32)]) for r in part]
            allres[name] = res
            report_incidents(name, res, out)
            report_waves(name, res, out)
    samp = [r['S'] for r in allres['Case B to 24 (exhaustive)'] if len(r['waves']) >= 2][::40] + \
           [r['S'] for r in allres['late band shapes']][::20]
    n, diff = scale_test(samp)
    out.write("\n== scale test (S vs 3S) on %d sets: sequences or incident descriptions differing %s\n" % (n, diff))
    out.close()
    print(open('wave_incident_v1.out').read()[len(__doc__):])
