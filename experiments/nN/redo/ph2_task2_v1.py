# ph2 Task 2: the effect of the fastest reading (rank 7).  Exact Fractions.  usage: python3 ph2_task2_v1.py MODE
#  MODE=big : members of cell_members_J2.pkl (leaf regions, rho_7<=17) with rho_7>9; all 59 gate-crossing ones + every 40th of the others
#  MODE=j1  : gate-crossing members of cell_members7_J1.pkl (rho_7<=9), removal test only
import pickle, sys, collections, time, math
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
def res(rhos):  # no sorting: index = identity; rhos[0] is the smallest (=1)
    steps, R = path(rhos)
    best = None
    for y, r in enumerate(rhos):
        j = 1
        while 8*j - 1 < R*r: j += 1
        e = F(8*j - 1)/r
        if best is None or e < best[0] or (e == best[0] and y < best[1][0]): best = (e, (y, j))
    word = tuple((s['setter']+1, s['lap']) for s in steps)
    states = [s['R'] for s in steps]
    return dict(word=word, R=R, closer=(best[1][0]+1, best[1][1]), states=states, steps=steps)
def blocks_at(R, r): return blocks(R, r)
def delete_one(w7, w6):
    if len(w7) != len(w6) + 1: return False
    return any(w7[:i] + w7[i+1:] == w6 for i in range(len(w7)))
def removal_class(r7, r6):
    if r7['word'] == r6['word']: return 'no effect (same path)' + (' / closer same' if r7['closer'] == r6['closer'] else ' / closer differs')
    if (r7['R'] > 7) != (r6['R'] > 7): return 'changes gate'
    if r7['R'] == r6['R'] and delete_one(r7['word'], r6['word']): return 'one extra move (landing same)'
    if r7['R'] != r6['R']: return 'changes landing (gate same)'
    return 'other: path differs, landing same, not a single deleted move'
def run_big(out, tmax):
    P = lambda *a: print(*a, file=out, flush=True)
    m = pickle.load(open('cell_members_J2.pkl', 'rb'))
    big = [x for x in m if x[1][6] > 9]
    t0 = time.time()
    for idx, r in big[:150]:  # agreement of res() with outcome()
        o = outcome(r); q = res(r)
        assert o['R'] == q['R'] and o['closer'] == q['closer'] and o['path'] == q['word']
    T = pickle.load(open('terminals5_J2.pkl', 'rb'))
    isgc = lambda idx: any(w[0] == 1 for w in T[idx][0])
    chk = collections.Counter((isgc(idx), path(r)[1] > 7) for idx, r in big[:3000] + big[-500:])
    P('members with rho_7>9: %d (J=2 leaf regions); region-path gate flag vs exact landing>7 on 3500 members (flag, landing>7): %s' % (len(big), sorted(chk.items())))
    flags = {n: None for n, (idx, r) in enumerate(big) if n % 40 == 0 or isgc(idx)}
    cnt = len(big)
    sel = [big[n] for n in sorted(flags)]
    P('flagged scan covered %d of %d members; selected %d (gate-crossing found + every 40th)' % (cnt, len(big), len(sel)))
    tally_rm = collections.Counter(); tally_rm_gc = collections.Counter(); tally_sh = collections.Counter(); tally_rep = collections.Counter()
    ruleA = collections.Counter(); exA = []; exS = []; ruleS = collections.Counter(); done = 0; fastcls = collections.Counter()
    for idx, r in sel:
        if time.time() - t0 > tmax: P('STOP processing at member %d of %d (time guard)' % (done, len(sel))); break
        done += 1
        r7 = res(r); r6 = res(r[:6]); gc = r7['R'] > 7
        c = removal_class(r7, r6); tally_rm[c] += 1
        if gc: tally_rm_gc[c] += 1
        w7_no7 = tuple(x for x in r7['word'] if x[0] != 7)
        a = (w7_no7 == r6['word']); ruleA[(gc, a)] += 1
        if not a and len(exA) < 4: exA.append((r, r7['word'], r6['word']))
        # activity of reading 7 in the 7-reading path: blocker at some visited state, or at the landing
        act = any(7-1 in s['blockers'] for s in r7['steps'])
        # replacements by a different faster reading
        for d in (F(1, 8), F(1, 2), F(1), F(2), F(4), F(8)):
            rr = r[:6] + [r[5] + d]
            tally_rep[removal_class(res(rr), r6).split(' /')[0] + ('' )] += 1
        # shifts of rho_7 by 8k/R_i
        states = r7['states'] + [r7['R']]
        for ii, Ri in enumerate(states):
            for k in (-2, -1, 1, 2):
                nr = r[6] + F(8*k)/Ri
                if nr <= 0 or nr in r[:6]: continue
                rs = res(r[:6] + [nr])
                where = 'first' if ii == 0 else ('landing' if ii == len(states)-1 else 'middle')
                if rs['word'] == r7['word'] and rs['closer'] == r7['closer']: cl = 'identical path, landing, closer'
                elif rs['word'] == r7['word']: cl = 'same path, closer differs'
                elif (rs['R'] > 7) != gc: cl = 'changes gate'
                elif rs['R'] != r7['R']: cl = 'changes landing'
                else: cl = 'path differs, landing same'
                tally_sh[cl] += 1; ruleS[(act, where, cl == 'identical path, landing, closer' or cl == 'same path, closer differs')] += 1
                if (not act) and cl in ('changes landing', 'changes gate') and len(exS) < 3: exS.append((r, ii, k, r7['word'], rs['word'], r7['R'], rs['R']))
    P('processed %d of %d selected members in %.0f s' % (done, len(sel), time.time() - t0))
    P('REMOVAL of rank 7 (6-reading cascade vs 7-reading cascade), classes over processed members:'); [P('   %-70s %d' % kv) for kv in sorted(tally_rm.items())]
    P('   among gate-crossing (7-reading landing>7) members only:'); [P('   %-70s %d' % kv) for kv in sorted(tally_rm_gc.items())]
    P('RULE A: "the 6-reading word = the 7-reading word with its moves set by rank 7 deleted": holds / fails by (gate-crossing?): %s' % sorted(ruleA.items()))
    for e in exA: P('   counterexample to RULE A: readings %s\n      7-word %s\n      6-word %s' % ([str(x) for x in e[0]], e[1], e[2]))
    P('REPLACEMENT of rank 7 by rho_6 + d, d in {1/8,1/2,1,2,4,8} (class relative to the 6-reading cascade; a "no effect" here also covers closer changes):'); [P('   %-70s %d' % kv) for kv in sorted(tally_rep.items())]
    P('SHIFT rho_7 -> rho_7 + 8k/R_i, k in {-2,-1,1,2}, R_i over the visited states and the landing (only rho_7\' > 0, distinct):'); [P('   %-70s %d' % kv) for kv in sorted(tally_sh.items())]
    P('   by (rank 7 blocks at some visited state in the original?, which R_i, unchanged-path?) counts: %s' % sorted(ruleS.items()))
    for e in exS: P('   exception example (rank 7 never blocks at a visited state, shift changes landing/gate): readings %s i=%d k=%d\n      word %s -> %s ; landing %s -> %s' % ([str(x) for x in e[0]], e[1], e[2], e[3], e[4], float(e[5]), float(e[6])))
def run_j1(out, tmax):
    P = lambda *a: print(*a, file=out, flush=True)
    m = pickle.load(open('cell_members7_J1.pkl', 'rb')); t0 = time.time()
    tally = collections.Counter(); tallyw = collections.Counter(); ruleA = collections.Counter(); ex = []; done = 0; gcn = 0
    for idx, r in m:
        if time.time() - t0 > tmax: P('STOP at member %d of %d' % (done, len(m))); break
        done += 1
        r7 = res(r)
        if r7['R'] <= 7: continue
        gcn += 1; r6 = res(r[:6]); c = removal_class(r7, r6); tally[c] += 1
        a = tuple(x for x in r7['word'] if x[0] != 7) == r6['word']; ruleA[a] += 1
        if not a and len(ex) < 3: ex.append((r, r7['word'], r6['word']))
    P('J=1 (all outcome regions, rho_7<=9): processed %d of %d; gate-crossing %d. REMOVAL of rank 7 classes:' % (done, len(m), gcn)); [P('   %-70s %d' % kv) for kv in sorted(tally.items())]
    P('RULE A holds/fails: %s' % sorted(ruleA.items()))
    for e in ex: P('   counterexample to RULE A: readings %s\n      7-word %s\n      6-word %s' % ([str(x) for x in e[0]], e[1], e[2]))
if __name__ == '__main__':
    mode = sys.argv[1]; out = open('ph2_task2_%s_v1.out' % mode, 'w')
    (run_big if mode == 'big' else run_j1)(out, 500)
    out.close()
