"""E237 (2026-10-01): why a one-reading move to the wall g = b0 sometimes changes the region (hole_perturb_v2.out).

Explanations, derived, checked here against every case:
  E1 (W_h, the overruns): the move of h reaches the wall iff g is the only instant of the block's relay from tau_C that
     lies past b0.  Otherwise an earlier relay instant past b0 is the exit of another block reading, which the move of h
     does not shift: g falls to that reading's exit and stays past b0 (region moved).
  E2 (W_c, all populations): if the move of c changes the region, then c sets tau_C (the core's own landing is c's exit,
     so the move shifts tau_C and the block's relay starts elsewhere), or tau_C jumps along the move.
"""
import sys, random
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
import hole_perturb_v2 as P
import hole3_cascade_v1 as H3, holef_cascade_v1 as HF


def one(job):
    tag, core, block = job
    st0 = P.state(core, block)
    if st0['h'] is None or st0['c'] is None:
        return tag, None, None
    out1 = None
    if tag == 'over':
        g, gm = P.relay(block, st0['tc'])
        past = [mv[3] for mv in gm if mv[3] > st0['b0']]
        only_g = (past == [g])
        fr, rr, nn, wd = P.wall_check(core, block, st0, 'W_h')
        moved = any(k.endswith('region moved') for k in rr)
        skipped = any('skipped' in k for k in rr)
        out1 = None if skipped else (only_g, moved, len(past))
    fr, rr, nn, wd = P.wall_check(core, block, st0, 'W_c')
    out2 = None
    if any(k.endswith('region moved') for k in rr):
        c = st0['c']; tcset = st0['tcset']
        sets_tc = (tcset != 'bound' and tcset[0] == c) or (tcset == 'bound' and core[0] == c)
        r, rw, _ = wd
        X = P.state(*P.swap(core, block, r, rw))
        jumped = X['tcset'] != st0['tcset'] if not sets_tc else False
        out2 = (sets_tc, jumped)
    elif not any('skipped' in k for k in rr):
        c = st0['c']; tcset = st0['tcset']
        out2 = ('kept', (tcset != 'bound' and tcset[0] == c) or (tcset == 'bound' and core[0] == c))
    return tag, out1, out2


if __name__ == '__main__':
    pop3 = H3.gen(232, 2000)
    popf = {f: HF.gen(f, 234 + f, 1000)[0] for f in (4, 5, 6)}
    with Pool(8) as pool:
        r3 = pool.map(HF.study, pop3, chunksize=25)
        rf = {f: pool.map(HF.study, popf[f], chunksize=25) for f in (4, 5, 6)}
    allr = [(3, r) for r in r3] + [(f, r) for f in (4, 5, 6) for r in rf[f]]
    over = [('over', r['core'], r['block']) for f, r in allr if r['k_land'] != 'S0']
    rng = random.Random(236); ctrl = []
    for f, n in ((3, 100), (4, 50), (5, 50), (6, 50)):
        cand = [r for g_, r in allr if g_ == f and r['k_land'] == 'S0' and r['passes'] and not r['at_tc']]
        ctrl += [('ctrl%d' % f, r['core'], r['block']) for r in rng.sample(cand, n)]
    with Pool(8) as pool:
        res = pool.map(one, over + ctrl)
    out = open('hole_perturb_regions_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    e1 = Counter((x[1][0], x[1][1]) for x in res if x[1] is not None)
    w("E1 overruns, (g the only relay instant past b0, region moved): %s" % dict(e1))
    w("   E1 holds iff every case is (True, False) or (False, True); failures: %d" % sum(v for (a, b), v in e1.items() if a == b))
    w("   relay instants past b0 when the region moved: %s" % dict(Counter(x[1][2] for x in res if x[1] is not None and x[1][1])))
    for tag in ('over', 'ctrl3', 'ctrl4', 'ctrl5', 'ctrl6'):
        e2 = Counter(x[2] for x in res if x[0] == tag and x[2] is not None)
        w("E2 %s, W_c: region moved as (c sets tau_C, tau_C jumped): %s; kept as ('kept', c sets tau_C): %s" % (
            tag, {k: v for k, v in e2.items() if k[0] != 'kept'}, {k: v for k, v in e2.items() if k[0] == 'kept'}))
    w("E2 failures (region moved, c does not set tau_C, no tau_C jump): %d" % sum(1 for x in res if x[2] == (False, False)))
    out.close()
    print(open('hole_perturb_regions_v1.out').read()[len(__doc__):])
