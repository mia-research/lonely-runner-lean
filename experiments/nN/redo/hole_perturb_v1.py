"""E236/E237 (2026-10-01): the hole paths perturbed through the cascade, one reading at a time.  Design: log E236.

g  = the block's relay landing from tau_C (first instant >= tau_C with the block clear), exit of block reading h on lap K;
b0 = the end of the core's first lonely stretch S0, core reading c on its entering edge on lap k (8 c b0 = 8k + 7).
Derived (A.9, C.5): the full set lands in S0 iff g <= b0; the landing leaves S0 at the wall h(8k+7) = c(8K+1).
  W_c: c -> c* = (8k+7)/(8g)  (slower = inside);   W_h: h -> h* = (8K+1)/(8 b0)  (faster = inside).
Checks at relative eta = 1e-9 either side of the wall:
  W1 inside: lands in S0 at g, within O(eta) of b0;   W2 outside: the path visits g and its next instant is c's exit on
  lap k+1, (8k+9)/(8c);   C1 at every wall-side point.
Walk: the moved reading in a straight line from its value to the wall (100 grid points, bisection at every change of the
landing's stretch index); each change classified: a g = b0 wall (any readings), a tau_C jump (relabels the stretches),
or other (listed in full).
Late entries: block reading b (lap L) setting the core's last move past tau_C; tie wall b* = (8L+1)/(8 tau_C).
  T1 at b*(1 +- eta): the same landing; the faster side passes through tau_C, the slower side does not.
A finite move that changes (h, K) or (c, k) at the wall is counted as region moved and listed, not failed.
"""
import sys, random
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8, next_opening
import hole3_cascade_v1 as H3
import holef_cascade_v1 as HF

ETA = F(1, 10 ** 9)
N = 100
TOL = F(1, 10 ** 6)


def relay(B, t):
    moves = []
    while True:
        way = [d for d in B if cd(d * t) < E8]
        if not way:
            return t, moves
        nx = max(next_opening(d, t) for d in way)
        moves.append((t, tuple(way), tuple(d for d in way if next_opening(d, t) == nx), nx))
        t = nx


def state(core, block):
    core = tuple(sorted(core)); block = tuple(sorted(block)); S = tuple(sorted(core + block))
    tc, cm = trace(core); ts, moves = trace(S)
    cells = [(a / 8, b / 8) for a, b in clear_set(list(core), 8 * tc, 8 * ts + 80 / core[0])]
    kl = next((i for i, (a, b) in enumerate(cells) if a <= ts <= b), None)
    g, gm = relay(block, tc)
    h = min(gm[-1][2]) if gm else None
    K = (8 * h * g - 1) / 8 if gm else None
    b0 = cells[0][1]
    cl = [c for c in core if (8 * c * b0) % 8 == 7]
    c = cl[0] if len(cl) == 1 else None
    k = (8 * c * b0 - 7) / 8 if c else None
    tcset = (min(cm[-1][2]), (8 * min(cm[-1][2]) * tc - 1) / 8) if cm else 'bound'
    return dict(core=core, block=block, S=S, tc=tc, ts=ts, moves=moves, insts=[mv[0] for mv in moves] + [ts], cells=cells,
                kl=kl, g=g, h=h, K=K, b0=b0, c=c, k=k, ncl=len(cl), tcset=tcset)


def swap(core, block, r, v):
    core = list(core); block = list(block)
    if r in core:
        core[core.index(r)] = v
    else:
        block[block.index(r)] = v
    S0 = sorted(list(core) + list(block)); old = sorted([r if x == v else x for x in S0])
    if len(set(S0)) != 7 or max(core) >= min(block) or S0.index(v) != sorted(old).index(r):
        return None
    return tuple(sorted(core)), tuple(sorted(block))


def c1_ok(st):
    S = st['S']
    cs = clear_set(list(S), 1 / S[0], 8 * st['ts'] + 1 / S[0])
    return bool(cs) and cs[0][0] == 8 * st['ts']


def classify(a, b):
    if abs(a['tc'] - b['tc']) > TOL * a['tc'] or a['tcset'] != b['tcset']:
        return 'tau_C jump (%s)' % ('landing continuous' if abs(a['ts'] - b['ts']) <= TOL * a['ts'] else 'landing jumps')
    if all(x['kl'] is not None and abs(x['g'] - x['b0']) <= TOL * x['b0'] for x in (a, b)) or \
            any(abs(x['g'] - x['b0']) <= TOL * x['b0'] for x in (a, b)):
        return 'g = b0 wall'
    return 'other'


def walk(core, block, r, rw, st0, inside_is_lower):
    """r moves from its value toward rw; returns list of (s, class, detail) for every change of kl before the wall."""
    pts = []
    for i in range(N):
        s = F(i, N); v = r + s * (rw - r)
        cb = swap(core, block, r, v) if i else (core, block)
        if cb is None:
            return None
        pts.append((s, cb, state(*cb) if i else st0))
    orig_inside = (st0['kl'] == 0)
    ve = rw * (1 - ETA) if (orig_inside == inside_is_lower) else rw * (1 + ETA)
    cb = swap(core, block, r, ve)
    if cb is None:
        return None
    pts.append(((ve - r) / (rw - r), cb, state(*cb)))
    ev = []
    for (sa, cba, a), (sb, cbb, b) in zip(pts, pts[1:]):
        if a['kl'] == b['kl']:
            continue
        lo, hi, A, B = sa, sb, a, b
        for _ in range(40):
            mid = (lo + hi) / 2; cbm = swap(core, block, r, r + mid * (rw - r))
            if cbm is None:
                break
            M = state(*cbm)
            if M['kl'] == A['kl']:
                lo, A = mid, M
            else:
                hi, B = mid, M
        ev.append((float(lo), classify(A, B), (A['kl'], B['kl']), (A['h'], A['K'], A['c'], A['k']), (B['h'], B['K'], B['c'], B['k'])))
    return ev


def wall_check(core, block, st0, which):
    fail = Counter(); rec = Counter(); notes = []
    h, K, c, k, g, b0 = st0['h'], st0['K'], st0['c'], st0['k'], st0['g'], st0['b0']
    if which == 'W_c':
        r, rw, lower_inside = c, F(8 * k + 7) / (8 * g), True
    else:
        r, rw, lower_inside = h, F(8 * K + 1) / (8 * b0), False
    vin, vout = (rw * (1 - ETA), rw * (1 + ETA)) if lower_inside else (rw * (1 + ETA), rw * (1 - ETA))
    cbi, cbo = swap(core, block, r, vin), swap(core, block, r, vout)
    if cbi is None or cbo is None:
        rec[which + ' skipped (the move changes the speed order)'] += 1
        return fail, rec, notes, None
    I, O = state(*cbi), state(*cbo)
    mv = lambda x: vin if x == r else x
    for side, X, v in (('inside', I, vin), ('outside', O, vout)):
        if not c1_ok(X):
            fail['C1 at %s %s' % (which, side)] += 1
        exp_h = v if (which == 'W_h') else h
        exp_c = v if (which == 'W_c') else c
        if (X['h'], X['K'], X['c'], X['k']) != (exp_h, K, exp_c, k):
            rec[which + ' region moved'] += 1
            notes.append((which, side, 'region moved', (X['h'], X['K'], X['c'], X['k']), (exp_h, K, exp_c, k)))
            return fail, rec, notes, None
    if I['kl'] == 0 and I['ts'] == I['g'] and abs(I['g'] - I['b0']) <= 1000 * ETA * I['b0']:
        rec[which + ' W1 inside lands in S0 at g, at b0'] += 1
    else:
        fail[which + ' W1'] += 1; notes.append((which, 'W1 fail', I['kl'], float(I['ts']), float(I['g']), float(I['b0'])))
    nxt = F(8 * O['k'] + 9) / (8 * O['c'])
    ins = O['insts']
    if O['kl'] is not None and O['kl'] >= 1 and O['g'] in ins and ins.index(O['g']) + 1 < len(ins) and ins[ins.index(O['g']) + 1] == nxt:
        rec[which + ' W2 outside: g visited, next move to c\'s exit on lap k+1'] += 1
    else:
        fail[which + ' W2'] += 1; notes.append((which, 'W2 fail', O['kl'], O['g'] in ins))
    return fail, rec, notes, (r, rw, lower_inside)


def study(args):
    tag, core, block = args
    st0 = state(core, block)
    fail = Counter(); rec = Counter(); notes = []; walks = []
    if tag == 'late':
        t, way, stt, nx = [mv for mv in st0['moves'] if mv[0] < st0['tc']][-1]
        b = min(stt); L = (8 * b * nx - 1) / 8; bw = F(8 * L + 1) / (8 * st0['tc'])
        cf, cs_ = swap(core, block, b, bw * (1 + ETA)), swap(core, block, b, bw * (1 - ETA))
        if cf is None or cs_ is None:
            rec['T1 skipped (order)'] += 1
        else:
            Fs, Ss = state(*cf), state(*cs_)
            same = abs(Fs['ts'] - Ss['ts']) <= 1000 * ETA * Fs['ts']
            pf, ps = Fs['tc'] in Fs['insts'], Ss['tc'] in Ss['insts']
            if same and pf and not ps:
                rec['T1 same landing; faster side passes tau_C, slower side does not'] += 1
            else:
                fail['T1'] += 1
            for X in (Fs, Ss):
                if not c1_ok(X):
                    fail['C1 at T1'] += 1
            Wt = state(*swap(core, block, b, bw))
            rec['T1 landing at the wall %s the original' % ('equals' if Wt['ts'] == st0['ts'] else 'differs from')] += 1
            notes.append(('T1', core, block, b, float(bw / b), float(st0['ts']), float(Wt['ts']), float(Fs['ts']), float(Ss['ts'])))
        return tag, core, block, fail, rec, notes, walks
    if st0['h'] is None or st0['c'] is None:
        rec['skipped (g = tau_C or two readings close S0)'] += 1
        return tag, core, block, fail, rec, notes, walks
    for which in ('W_c', 'W_h'):
        f_, r_, n_, wd = wall_check(core, block, st0, which)
        fail.update(f_); rec.update(r_); notes += n_
        if wd:
            r, rw, lower_inside = wd
            ev = walk(core, block, r, rw, st0, lower_inside)
            if ev is None:
                rec[which + ' walk skipped (order)'] += 1
            else:
                rec[which + ' walk: changes of the landing stretch before the wall = %d' % len(ev)] += 1
                for e in ev:
                    rec[which + ' walk change: ' + e[1]] += 1
                walks.append((which, ev))
    return tag, core, block, fail, rec, notes, walks


if __name__ == '__main__':
    pop3 = H3.gen(232, 2000)
    popf = {f: HF.gen(f, 234 + f, 1000)[0] for f in (4, 5, 6)}
    with Pool(8) as pool:
        r3 = pool.map(HF.study, pop3, chunksize=25)
        rf = {f: pool.map(HF.study, popf[f], chunksize=25) for f in (4, 5, 6)}
    allr = [(3, r) for r in r3] + [(f, r) for f in (4, 5, 6) for r in rf[f]]
    over = [('over', r['core'], r['block']) for f, r in allr if r['k_land'] != 'S0']
    late = [('late', r['core'], r['block']) for f, r in allr if not r['passes']]
    rng = random.Random(236); ctrl = []
    for f, n in ((3, 100), (4, 50), (5, 50), (6, 50)):
        cand = [r for g_, r in allr if g_ == f and r['k_land'] == 'S0' and r['passes'] and not r['at_tc']]
        ctrl += [('ctrl%d' % f, r['core'], r['block']) for r in rng.sample(cand, n)]
    jobs = over + late + ctrl
    with Pool(8) as pool:
        res = pool.map(study, jobs, chunksize=2)
    out = open('hole_perturb_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for name, sel in (('the 30 overruns', 'over'), ('the 6 late entries', 'late'), ('controls f = 3', 'ctrl3'),
                      ('controls f = 4', 'ctrl4'), ('controls f = 5', 'ctrl5'), ('controls f = 6', 'ctrl6')):
        grp = [x for x in res if x[0] == sel]
        Fa = Counter(); Ra = Counter()
        for x in grp:
            Fa.update(x[3]); Ra.update(x[4])
        w("\n== %s: %d configurations ==" % (name, len(grp)))
        w("  FAILURES (pass: none): %s" % (dict(Fa) if Fa else 'none'))
        for k_, v in sorted(Ra.items()):
            w("  %s: %d" % (k_, v))
        for x in grp:
            for n_ in x[5]:
                if n_[0] == 'T1' or 'fail' in str(n_[1]) or n_[2] == 'region moved':
                    w("    note %s %s: %s" % (x[1], x[2], n_))
            for which, ev in x[6]:
                for e in ev:
                    if e[1] != 'g = b0 wall':
                        w("    walk %s %s %s: s=%.6f %s stretch %s -> %s; (h,K,c,k) %s -> %s" % (x[1], x[2], which, e[0], e[1], e[2][0], e[2][1], e[3], e[4]))
    out.close()
    print(open('hole_perturb_v1.out').read()[len(__doc__):])
