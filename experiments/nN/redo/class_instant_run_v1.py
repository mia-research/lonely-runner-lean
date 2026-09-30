"""E216/E217 (2026-10-01): the re-aimed run.  The class instant on the arrangement's own grid: what selects it, how the
speed moves it.  Design: log E216.  No window, no lap restriction; M = ceil(mm*m/e) is a coordinate; the range M <= 4 is a
range of search, not a statement (every set with no lonely class instant in it is listed).

Object (corrected in E217 from E216's).  After the pair law's rescaling (a on its grid point) the class instant depends
only on the leaving-edge reading a, its grid point n_a and the class c: the grid through a with divisor n_a, class c,
c*n_a = 8K+1.  So the family is the readings' openings (8K+1)/(8a), each read as class c of the grid through a with
n_a = (8K+1)/c.  At t = c*n_a/(8a) reading d has rescaled grid point n' = round(n_a*d/a), residue r' = c*n' mod 8,
deviation eps' = c*(n_a*d/a - n'); clear iff (c*n_a*d) mod 8a in [a, 7a].
Kinds of failure (the reading is in the way; named by its rescaled residue): captured (r' = 0), entering edge passed
(r' = 7), leaving edge not reached (r' = 1), interior beyond band (r' in 2..6).  E216's M4-3 was false as stated: a
residue-7 reading can be clear with eps' >= 2 (past the next leaving edge); it is dropped.
Part A (placement) and Part B (relocation) as in E216.  Checks: C1 (the cascade's landing equals the least clear point
from clear_set); M4-2 (mirror residues); M4-3 (residue-7 readings have eps <= 0 at lonely instants); the integer test
against Fraction positions at lonely instants.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8

MCAP = 4


def evaluate(S, c, a, na):
    """The class-c instant of the grid through reading a with divisor na (a on its grid point, the pair law's rescaling):
    t = c*na/(8a), a's opening.  Per reading: rescaled grid point n' = round(na*d/a), residue r' = c*n' mod 8,
    eps' = c*(na*d/a - n'), clear by the integer test."""
    top = c * na; rows = []
    for d in S:
        n1 = (2 * na * d + a) // (2 * a)
        q = (top * d) % (8 * a)
        rows.append(((c * n1) % 8, F(top * d, a) - c * n1, a <= q <= 7 * a, d))
    return F(top, 8 * a), rows


def kind(r, eps):
    if r == 0:
        return 'captured'
    if r == 7:
        return 'entering edge passed'
    if r == 1:
        return 'leaving edge not reached'
    return 'interior beyond band'


def instants(S):
    """Every class instant in the range: key (a, na, c) -> (t, rows).  The range na*m <= MCAP*a (grid step >= m/MCAP)
    is a range of search; since t = c*na/(8a), it is the window R = 8mt <= c*MCAP."""
    S = tuple(sorted(S)); m = S[0]; out = {}
    for a in S:
        for na in range(1, MCAP * a // m + 1):
            for c in (1, 3, 5, 7):
                if (c * na) % 8 == 1:
                    out[(a, na, c)] = evaluate(S, c, a, na)
    return out


def landing(S):
    S = tuple(sorted(S)); m = S[0]
    ts, moves = trace(S)
    R = 8 * m * ts
    least = clear_set([F(d, m) for d in S], F(1), max(F(40), R + 1))[0][0]
    return ts, (least == R)


def study_a(S):
    S = tuple(sorted(S)); I = instants(S)
    lonely = {k: v for k, v in I.items() if all(x[2] for x in v[1])}
    chk = 0
    for k, (t, rows) in lonely.items():
        chk += sum(1 for r, eps, cl, d in rows if cd(d * t) < E8)                          # integer vs Fraction
    for (a, na, c), (t, rows) in I.items():
        chk += sum(1 for r, eps, cl, d in rows if d == a and (r != 1 or eps != 0))        # construction
    kinds = Counter(); only_entering = 0; mirror = Counter(); mirror_kinds = Counter(); beyond = Counter()
    for k, (t, rows) in I.items():
        if k in lonely:
            interior = [abs(eps) for r, eps, cl, d in rows if 2 <= r <= 6]
            beyond['largest interior |eps| <= 1' if max(interior, default=0) <= 1 else 'largest interior |eps| > 1'] += 1
            continue
        bad = [(r, eps, d) for r, eps, cl, d in rows if not cl]
        for r, eps, d in bad:
            kinds[kind(r, eps)] += 1
        if all(r == 7 for r, eps, d in bad):
            only_entering += 1
            a, na, c = k
            for r, eps, b in bad:
                nb = (2 * na * b + a) // (2 * a)
                chk += (((8 - c) * nb) % 8 != 1)                                               # M4-2
                t2, rows2 = evaluate(S, 8 - c, b, nb)
                ok = all(x[2] for x in rows2)
                mirror['mirror lonely' if ok else 'mirror not lonely'] += 1
                if not ok:
                    for r2, eps2, cl2, d2 in rows2:
                        if not cl2:
                            mirror_kinds[kind(r2, eps2)] += 1
    ts, c1 = landing(S)
    chk += (not c1)
    land_in = any(v[0] == ts for v in lonely.values())
    return dict(S=S, n_inst=len(I), n_lonely=len(lonely), kinds=kinds, only_entering=only_entering,
                mirror=mirror, mirror_kinds=mirror_kinds, beyond=beyond, land_in=land_in, chk=chk)


def report_a(name, rows, w):
    w("\n== A. %s: %d sets ==" % (name, len(rows)))
    w("  CHECKS (C1, M4-2, construction, integer vs Fraction): %d failures" % sum(r['chk'] for r in rows))
    miss = [r['S'] for r in rows if r['n_lonely'] == 0]
    w("  sets with no lonely class instant in the range (R <= 7*%d): %d %s" % (MCAP, len(miss), miss[:20]))
    K = Counter(); O = 0; Mi = Counter(); MK = Counter(); B = Counter()
    for r in rows:
        K.update(r['kinds']); O += r['only_entering']; Mi.update(r['mirror']); MK.update(r['mirror_kinds']); B.update(r['beyond'])
    w("  failing readings at non-lonely class instants, by kind: %s" % dict(K))
    w("  class instants failing only on the entering edge (the pair law's case): %d; their mirrors: %s" % (O, dict(Mi)))
    w("  kinds failing those mirrors: %s" % dict(MK))
    w("  lonely class instants by the largest interior deviation (grid_pair_law's hypothesis is |eps| <= 1): %s" % dict(B))
    w("  the cascade's landing is one of the set's lonely class instants: %s (FORCED whenever the landing lies in the"
      " search window R <= 7*%d: the landing is a lonely opening)" % (dict(Counter(r['land_in'] for r in rows)), MCAP))


# ---------------- B: relocation -------------------------------------------------------------------------------
def sweep(args):
    S0, j = args
    S0 = tuple(sorted(S0)); name0 = S0[j]
    prev = None; events = []; chk = 0; land_track = Counter(); empty = []
    for dl in range(-150, 151, 5):
        U = list(S0); U[j] = name0 + dl
        if len(set(U)) < 7 or min(U) != S0[0] or U[j] <= S0[0]:
            continue
        S = tuple(sorted(U)); rename = {d: (name0 if d == U[j] else d) for d in S}
        I = instants(S)
        L = {}
        for (a, na, c), (t, rows) in I.items():
            if all(x[2] for x in rows):
                L[(rename[a], na, c)] = (t, rows, S)
        ts, c1 = landing(S); chk += (not c1)
        land_track['landing is a lonely class instant' if any(v[0] == ts for v in L.values()) else 'landing is not'] += 1
        if not L:
            empty.append((S, dl))
        if prev is not None:
            ended = set(prev) - set(L); begun = set(L) - set(prev)
            ended_entering = {}
            for k in ended:
                a, na, c = k
                cur = I.get((a if a != name0 else U[j], na, c))
                if cur is None:
                    events.append(('ended', 'outside the range after the move', None)); continue
                bad = [(r, eps, rename[d]) for r, eps, cl, d in cur[1] if not cl]
                for r, eps, d in bad:
                    events.append(('ended', kind(r, eps), 'the moved reading' if d == name0 else 'another reading'))
                    if r == 7:
                        ended_entering.setdefault(d, set()).add(c)
            for k in begun:
                a, na, c = k
                if a in ended_entering and (8 - c) in ended_entering[a]:
                    rel = 'the mirror of an ended instant (its entering-edge reading, class 8 - c)'
                elif any(k2[0] == a for k2 in ended):
                    rel = 'the same leaving-edge reading, another lap'
                else:
                    rel = 'another leaving-edge reading'
                events.append(('begun', rel, None))
        prev = L
    return dict(S=S0, j=j, events=events, chk=chk, land=land_track, empty=empty)


def fine(seed, n, lo, hi):
    r = random.Random(seed); out = []
    while len(out) < n:
        m = 1000; W = int(r.uniform(lo, hi) * m)
        S = tuple(sorted({m, W} | {r.randrange(m + 1, W) for _ in range(5)}))
        if len(S) == 7:
            out.append(S)
    return out


if __name__ == '__main__':
    out = open('class_instant_run_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    p1 = list(itertools.combinations(range(1, 17), 7))
    rng = random.Random(216); p2 = []
    while len(p2) < 2000:
        p2.append(tuple(sorted(rng.sample(range(1, 201), 7))))
    p3 = fine(217, 1000, 2, 20)
    with Pool(8) as pool:
        for name, pop in (('every 7-set of readings <= 16', p1), ('uniform 7-sets of readings <= 200', p2),
                          ('fine shapes, least reading 1,000, spread uniform in [2, 20]', p3)):
            report_a(name, pool.map(study_a, pop, chunksize=20), w)
        shapes = fine(218, 30, 2, 20)
        res = pool.map(sweep, [(S, j) for S in shapes for j in range(1, 7)])
    w("\n== B. relocation: 30 fine shapes, each reading moved -150..+150 in steps of 5 (%d sweeps) ==" % len(res))
    w("  CHECK C1 over every step: %d failures" % sum(r['chk'] for r in res))
    ev = Counter(); land = Counter(); empties = []
    for r in res:
        ev.update((a, b, c) for a, b, c in r['events']); land.update(r['land']); empties += r['empty']
    for k, v in sorted(ev.items(), key=lambda kv: (kv[0][0], -kv[1])):
        w("  %s | %s | %s: %d" % (k[0], k[1], k[2] or '', v))
    w("  landing at each step: %s" % dict(land))
    w("  steps with no lonely class instant for M <= %d: %d %s" % (MCAP, len(empties), empties[:20]))
    out.close()
    print(open('class_instant_run_v1.out').read()[len(__doc__):])
