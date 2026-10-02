# Step rules for the cascade.  Usage: python3 pred_step_rules_v1.py  (2 worker processes)
import sys, random, time, pickle
from collections import Counter, defaultdict
from math import floor
exec(open('pred_lib_v1.py').read())
def lap_at(R, r): return int(floor(R * r / 8 + F(1, 2)))
def closure(xs, cap=3000):
    """static closure: zones reachable from zones containing R0 by 'exit of Z lies in zone Z'' (all branches, no max rule)."""
    R0 = 1 / min(xs); seen = set(); stack = []; over = False
    def zs(R):
        return [(y, lap_at(R, r)) for y, r in enumerate(xs) if blocks(R, r)]
    for z in zs(R0):
        seen.add(z); stack.append(z)
    while stack:
        y, j = stack.pop(); e = (8 * j + 1) / xs[y]
        if e > cap: over = True; continue
        for z in zs(e):
            if z not in seen and len(seen) < 5000: seen.add(z); stack.append(z)
    return seen, over
def analyze(xs):
    C = Counter(); ex = []
    steps, Rend = path(xs); n = len(steps); R0 = 1 / min(xs)
    C['arr'] += 1; C['moves=%d' % min(n, 12)] += 1
    # ---- (a)
    for k, s in enumerate(steps):
        C['steps'] += 1; R = s['R']; bl = s['blockers']
        zc = zones_containing(R, xs)
        if sorted(z[0] for z in zc) != sorted(bl) or len(zc) != len(bl): C['A1_viol'] += 1; ex.append(('A1', xs, k))
        jb = {y: j for y, j, _ in zc}
        if any(jb[y] != lap_at(R, xs[y]) for y in bl): C['A1b_viol'] += 1
        mx = max(e for _, _, e in zc); arg = [y for y, j, e in zc if e == mx]
        if s['setter'] not in arg or (8 * s['lap'] + 1) / xs[s['setter']] != mx: C['A2_viol'] += 1; ex.append(('A2', xs, k))
        if len(arg) > 1: C['A2_ties'] += 1
        # exit offset form: jump = (1 - p)/rho where p = R*rho - 8j
        if any(s['R2'] - R != (1 - (R * xs[y] - 8 * jb[y])) / xs[y] for y in [s['setter']]): C['A2c_viol'] += 1
        if (8 * s['lap'] + 1) / xs[s['setter']] != s['R2']: C['A2d_viol'] += 1
        # lowest-rank blocker rule
        x = min(bl); y = s['setter']
        C['bl_count=%d' % len(bl)] += 1
        rk = sorted(bl).index(y); C['setter_rank_among_blockers=%d' % min(rk, 4)] += 1
        if len(bl) == 1: C['single_blocker'] += 1
        if y == x or (len(arg) > 1 and x in arg): C['lowest_rank_agrees'] += 1
        else:
            C['lowest_rank_fails'] += 1
            jx, jy = jb[x], jb[y]
            if len(bl) == 1: C['LR_viol'] += 1
            if not (y > x and jy > jx and (8 * jy + 1) * xs[x] > (8 * jx + 1) * xs[y]): C['fail_char_viol'] += 1
            C['fail_lap_gap=%d' % min(jy - jx, 5)] += 1
            C['fail_in_blockers_of_size=%d' % len(bl)] += 1
            C['fail_step_index=%d' % min(k, 5)] += 1
            ex.append(('LRfail', xs, k, x, jx, y, jy))
            if k == 0: C['fail_at_first_step'] += 1
        # pair rule: among the blockers, y beats x iff (8jy+1)rho_x > (8jx+1) rho_y
        pv = 0
        for a in bl:
            for b in bl:
                if a != b:
                    beats = (8 * jb[a] + 1) * xs[b] > (8 * jb[b] + 1) * xs[a]
                    if beats and (8 * jb[a] + 1) / xs[a] <= (8 * jb[b] + 1) / xs[b]: pv += 1
        if pv: C['pair_viol'] += 1
        # ---- (b) link rule at R2
        R2 = s['R2']; ss = s['setter']; js = s['lap']
        for y2, r in enumerate(xs):
            if y2 == ss: continue
            b2 = blocks(R2, r); j2 = lap_at(R2, r)
            if not b2: continue
            slow = r < xs[ss]; C['link_new_%s' % ('slower' if slow else 'faster')] += 1
            if slow:
                if j2 > js: C['link_viol_slower'] += 1; ex.append(('Lslow', xs, k, y2))
                C['link_slower_lap_%s' % ('same' if j2 == js else 'lower')] += 1
            else:
                if j2 <= js: C['link_viol_faster'] += 1; ex.append(('Lfast', xs, k, y2))
                C['link_faster_lapdiff=%d' % min(j2 - js, 4)] += 1
            if y2 in bl:
                C['returned'] += 1
                if j2 <= jb[y2]: C['returned_lap_viol'] += 1
            else: C['carried'] += 1
            if lap_at(R, r) > j2: C['lap_decrease_viol'] += 1
        # readings that block at R2 : exactly those with dist((8js+1) rho/rho_s, 8Z) < 1  (check)
        pred = [y2 for y2, r in enumerate(xs) if y2 != ss and min(((8 * js + 1) * r / xs[ss]) % 8, 8 - ((8 * js + 1) * r / xs[ss]) % 8) < 1]
        act = [y2 for y2, r in enumerate(xs) if y2 != ss and blocks(R2, r)]
        if pred != act: C['ratio_test_viol'] += 1
        if blocks(R2, xs[ss]): C['setter_still_blocks_viol'] += 1
        # next setter
        if k + 1 < n:
            ns = steps[k + 1]; y3 = ns['setter']; j3 = ns['lap']
            if y3 == ss: C['next_same_reading'] += 1; 
            elif xs[y3] < xs[ss]: C['next_setter_slower'] += 1
            else: C['next_setter_faster'] += 1
            if abs(ns['R'] - R2) != 0: C['markov_viol'] += 1
    # landing
    if zones_containing(Rend, xs): C['landing_viol'] += 1
    # first setter strip rule (restated)
    # ---- (c)
    setters = [s['setter'] for s in steps]; blk = set(y for s in steps for y in s['blockers'])
    cl, over = closure(xs); clr = set(y for y, j in cl)
    C['readings'] += 7; C['setter_readings'] += len(set(setters)); C['blocker_readings'] += len(blk)
    C['closure_readings'] += len(clr); C['closure_over'] += over
    zs = set((s['setter'], s['lap']) for s in steps)
    bzs = set((y, lap_at(s['R'], xs[y])) for s in steps for y in s['blockers'])
    if not bzs <= cl: C['closure_zone_viol'] += 1; ex.append(('Cviol', xs))
    if not blk <= clr: C['closure_reading_viol'] += 1
    C['closure_zones'] += len(cl); C['blocker_zones'] += len(bzs)
    C['readings_in_closure_not_blocker'] += len(clr - blk); C['readings_not_in_closure'] += 7 - len(clr)
    C['readings_not_blocker'] += 7 - len(blk); C['readings_not_setter'] += 7 - len(set(setters))
    # inert = never setter ; blockers-not-setters
    C['blocker_not_setter'] += len(blk - set(setters))
    # ---- (d)
    feat = dict(n=n, strip0=len(steps[0]['blockers']) if steps else 0, distinct=len(set(setters)), maxlap=max([s['lap'] for s in steps], default=0),
                R0=R0, Rend=Rend, setters=tuple(x + 1 for x in setters), laps=tuple(s['lap'] for s in steps), repeats=n - len(set(setters)),
                first_strip=sum(1 for r in xs if 7 < r < 9),
                nstrip=sum(1 for r in xs if any(8 * j - 1 < r < 8 * j + 1 for j in range(1, 100))))
    return C, ex[:3], feat
def work(args):
    name, seed, N = args
    f = dict(FAMS)[name]; rnd = random.Random(seed); C = Counter(); ex = []; feats = []
    for _ in range(N):
        xs = f(rnd); c, e, ft = analyze(xs); C.update(c); ex += e[:2]; ft['fam'] = name; ft['rho'] = tuple(xs); feats.append(ft)
    return name, C, ex[:30], feats
if __name__ == "__main__":
    from multiprocessing import Pool
    plan = [("random", 11, 6000), ("AP deformed", 12, 6000), ("strip_multi", 13, 8000), ("first_strip", 14, 4000), ("chain", 15, 14000), ("chain", 16, 8000),
            ("climb", 17, 1000), ("climb", 18, 1000), ("climb", 19, 1000), ("climb", 20, 1000)]
    t = time.time(); tot = Counter(); allf = []; allex = []
    with Pool(2) as p:
        for name, C, ex, feats in p.imap_unordered(work, plan):
            print("== %s : arr %d steps %d  (%.0fs)" % (name, C['arr'], C['steps'], time.time() - t)); sys.stdout.flush()
            tot.update(C); allf += feats; allex += [(name,) + e for e in ex]
            pickle.dump((tot, allf, allex), open('pred_step_rules_v1.pkl', 'wb'))
    print("\nTOTAL"); 
    for k in sorted(tot): print("  %-40s %d" % (k, tot[k]))
    print("\nexample records (first few):")
    for e in allex[:12]: print("  ", e[0], e[1], [str(x) if not isinstance(x, (tuple, list)) else [str(v) for v in x] for x in e[2:3]], e[3:])
