"""E223 (2026-10-01): the Level C catalogue checked (docs/n8/CASCADE_ACCOUNT_LEVEL_C_v1.md, C.8).

Owner: "Yes on to the next, if it not large then continue on to other too".  M8: derived items, checked; pass condition
0 failures.  Exact rational speeds; the cascade is `e151_block_v1.trace` (BSM, strict).  Crossings at relative eta.
  C1  margins along the chain; a random perturbation inside them leaves the chain (setter ranks, laps, landing) unchanged.
  C3  a tie wall between a crowd member and the setter: both sides land at the same certificate; setter ranks differ in
      at most one move.
  C4  an edge wall at an intermediate exit: both sides land at the same certificate, except where the wall is also a face
      of the landing's box (the reading on an edge at the landing) or of an earlier certificate's box (the wall instant
      lonely on one side, before the landing): those are counted as the derived exceptions.
  C5  the landing's faces: inside lands at the certificate (else counted, region moved); outside, leaving face: hand-off
      to d's opening on lap k_d, instant within O(eta); entering face: the old landing is visited and the next instant is
      d's exit on lap k_d + 1; never an earlier landing.
Populations: 300 seeded fine shapes; 300 late band shapes drawn uniformly; 300 sets drawn uniformly from readings <= 16.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8

ETA = F(1, 10 ** 9)


def chain(S):
    S = tuple(sorted(S)); ts, moves = trace(S)
    rank = {d: i for i, d in enumerate(S)}
    h = min(moves[-1][2]) if moves else S[0]
    K = (8 * h * ts - 1) / 8
    seq = tuple((tuple(sorted(rank[a] for a in st)), (8 * min(st) * nx - 1) / 8) for t, way, st, nx in moves)
    return dict(S=S, ts=ts, moves=moves, h=h, K=K, land=(rank[h], K), seq=seq, rank=rank)


def edge_dist(p):
    r = p % 8
    return min(abs(r - 1), abs(r - 7), r + 1, 9 - r)


def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)


def margins(C):
    S = C['S']; m = S[0]; eps = []
    inst = [(F(1, 8 * m), (m,))] + [(nx, st) for t, way, st, nx in C['moves']]
    for tau, st in inst:
        for b in S:
            if b in st:
                continue
            p = 8 * b * tau; dl = edge_dist(p)
            eps.append(dl / (2 * p + 2 * dl) if p > 0 else F(1))
    for t, way, st, nx in C['moves']:
        ex = sorted((F(8 * round(c * t) + 1, 8 * c) for c in way), reverse=True)
        for e in ex[1:]:
            g = (ex[0] - e) / ex[0]
            eps.append(g / (2 + g))
    for a, b in zip(S, S[1:]):
        eps.append((b - a) / (b + a))
    return min(eps)


def with_value(S, old, new):
    U = [new if d == old else d for d in S]
    return tuple(sorted(U)) if len(set(U)) == 7 and sorted(U).index(new) == sorted(S).index(old) else None


def study(S):
    S = tuple(sorted(F(d) for d in S))
    C = chain(S); rng = random.Random(hash(S) & 0xffffffff)
    fail = Counter(); rec = Counter()
    # C1
    e = margins(C)
    if e == 0:
        rec['C1 on a wall (not perturbed)'] += 1
    else:
        e = e / 4
        for _ in range(3):
            U = tuple(d * (1 + F(rng.randint(-1000, 1000), 1000) * e) for d in S)
            if tuple(sorted(U)) != U:
                fail['C1 order changed'] += 1; continue
            C2 = chain(U)
            if C2['seq'] != C['seq'] or C2['land'] != C['land']:
                fail['C1 chain changed'] += 1
            else:
                rec['C1 perturbations unchanged'] += 1
    # C3: tie walls
    for t, way, st, nx in C['moves']:
        a = min(st); k = (8 * a * nx - 1) / 8
        for c in way:
            if c in st:
                continue
            lc = round(c * t)
            cw = F(8 * lc + 1) * a / (8 * k + 1)
            if not (8 * lc - 1 < 8 * cw * t < 8 * lc + 1):
                rec['C3 skipped (slot changes)'] += 1; continue
            Up = with_value(S, c, cw * (1 + ETA)); Um = with_value(S, c, cw * (1 - ETA))
            if Up is None or Um is None:
                rec['C3 skipped (order)'] += 1; continue
            Cp, Cm = chain(Up), chain(Um)
            if Cp['land'] != Cm['land']:
                last = (C['moves'][-1][3] == nx)
                cont = abs(Cp['ts'] - Cm['ts']) <= Cp['ts'] * 1000 * ETA
                hand = {Cp['h'], Cm['h']} == {cw * (1 + ETA), a} or {Cp['h'], Cm['h']} == {cw * (1 - ETA), a}
                if last and cont and hand:
                    rec['C3 tie at the final move: the landing hands off (derived, C.3 as repaired)'] += 1
                else:
                    fail['C3 landing differs, unexplained'] += 1
            else:
                diff = sum(1 for x, y in zip(Cp['seq'], Cm['seq']) if x != y) + abs(len(Cp['seq']) - len(Cm['seq']))
                rec['C3 same landing; setter changes in %s moves' % ('<= 1' if diff <= 1 else '> 1')] += 1
    # C4: intermediate edge walls
    for j, (t, way, st, nx) in enumerate(C['moves'][:-1]):
        a = min(st); k = (8 * a * nx - 1) / 8
        for b in S:
            if b in st:
                continue
            p = b * (8 * k + 1) / a
            r = p % 8; base = p - r
            cands = [base - 1, base + 1, base + 7, base + 9]
            edge = min(cands, key=lambda x: abs(x - p))
            if edge <= 0:
                continue
            bw = edge * a / (8 * k + 1)
            Up = with_value(S, b, bw * (1 + ETA)); Um = with_value(S, b, bw * (1 - ETA)); Uw = with_value(S, b, bw)
            if Up is None or Um is None or Uw is None:
                rec['C4 skipped (order)'] += 1; continue
            Cp, Cm, Cw = chain(Up), chain(Um), chain(Uw)
            if Cp['land'] == Cm['land']:
                rec['C4 same landing'] += 1
                if Cp['seq'] != Cm['seq']:
                    rec['C4 same landing, route changed'] += 1
                continue
            on_face = (8 * bw * Cw['ts']) % 8 in (1, 7)
            earlier = nx < max(Cp['ts'], Cm['ts']) and (lonely(Up, nx) != lonely(Um, nx))
            if on_face:
                rec['C4 landing differs: also a face of the landing box (derived)'] += 1
            elif earlier:
                rec['C4 landing differs: also a face of an earlier box (derived)'] += 1
            else:
                fail['C4 landing differs, unexplained'] += 1
    # C5: landing faces
    h, K, ts = C['h'], C['K'], C['ts']
    for d in S:
        if d == h:
            continue
        kd = math.floor((8 * d * ts - 1) / 8)
        for face, num, inside_sign in (('leaving', 8 * kd + 1, 1), ('entering', 8 * kd + 7, -1)):
            Fv = F(num) * h / (8 * K + 1)
            Ui = with_value(S, d, Fv * (1 + inside_sign * ETA)); Uo = with_value(S, d, Fv * (1 - inside_sign * ETA))
            if Ui is None or Uo is None or Fv <= 0:
                rec['C5 skipped (order)'] += 1; continue
            Ci = chain(Ui)
            if Ci['h'] != h or Ci['K'] != K:
                rec['C5 region moved (inside landing differs)'] += 1; continue
            Co = chain(Uo); dn = Fv * (1 - inside_sign * ETA)
            tight = any((8 * x * Ci['ts']) % 8 in (1, 7) for x in Ui if x not in (h, Fv * (1 + inside_sign * ETA)))
            if tight:
                rec['C5 skipped (another reading tight at the landing)'] += 1; continue
            if Co['ts'] < Ci['ts'] - Ci['ts'] * 1000 * ETA:
                Uw = with_value(S, d, Fv); Cw = chain(Uw)
                if Cw['ts'] < ts and (8 * Fv * Cw['ts']) % 8 in (1, 7):
                    rec['C5 earlier landing: the face is also a face of an earlier box (coincident walls, derived)'] += 1
                else:
                    fail['C5 earlier landing at an infinitesimal crossing, unexplained'] += 1
                continue
            if face == 'leaving':
                if Co['h'] == dn and (8 * dn * Co['ts'] - 1) / 8 == kd and abs(Co['ts'] - Ci['ts']) <= Ci['ts'] * 1000 * ETA:
                    rec['C5 leaving: hand-off'] += 1
                else:
                    fail['C5 leaving: not a hand-off'] += 1
            else:
                insts = [mv[0] for mv in Co['moves']] + [Co['ts']]
                nxt_d = F(8 * kd + 9, 8) / dn
                if ts in insts and insts.index(ts) + 1 < len(insts) and insts[insts.index(ts) + 1] == nxt_d:
                    rec['C5 entering: next move to d\'s exit; %s' % ('lonely there' if Co['ts'] == nxt_d else 'relay continues')] += 1
                else:
                    fail['C5 entering: route or next move differs'] += 1
    return fail, rec


def run(sets):
    Fa = Counter(); Ra = Counter()
    for S in sets:
        f, r = study(S); Fa.update(f); Ra.update(r)
    return Fa, Ra


def fine(seed, n, lo, hi):
    r = random.Random(seed); out = []
    while len(out) < n:
        m = 1000; W = int(r.uniform(lo, hi) * m)
        S = tuple(sorted({m, W} | {r.randrange(m + 1, W) for _ in range(5)}))
        if len(S) == 7:
            out.append(S)
    return out


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    rng = random.Random(223)
    pops = [('300 seeded fine shapes', fine(223, 300, 2, 20)),
            ('300 late band shapes drawn uniformly', rng.sample(late_shapes(), 300)),
            ('300 sets drawn uniformly from readings <= 16', rng.sample(list(itertools.combinations(range(1, 17), 7)), 300))]
    out = open('cascade_level_c_check_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    with Pool(8) as pool:
        for name, sets in pops:
            res = pool.map(run, [sets[i::32] for i in range(32)])
            Fa = Counter(); Ra = Counter()
            for f, r in res:
                Fa.update(f); Ra.update(r)
            w("\n== %s ==" % name)
            w("  FAILURES (pass: none): %s" % (dict(Fa) if Fa else 'none'))
            for k_, v in sorted(Ra.items()):
                w("  %s: %d" % (k_, v))
    out.close()
    print(open('cascade_level_c_check_v1.out').read()[len(__doc__):])
