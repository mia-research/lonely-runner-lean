# Exhaustive integer 7-subsets {s=a1<a2<..<a7<=A7max} with gcd(a)=1, readings a_i/s. Chunked by a7=M, checkpointed.
# usage: lat_enum2_v1.py s A7max budget_seconds        state: lat_state2_s{s}_v1.pkl
import sys, os, pickle, time
from fractions import Fraction as F
from itertools import combinations
from math import gcd, floor
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
def outcome_from(rhos, steps, R):
    opener = (steps[-1]['setter'] + 1, steps[-1]['lap']) if steps else None
    best = None
    for y, r in enumerate(rhos):
        j = max(1, -(-(R * r + 1) // 8)); j = int(j)
        while 8 * j - 1 < R * r: j += 1
        while j > 1 and 8 * (j - 1) - 1 >= R * r: j -= 1
        e = F(8 * j - 1) / r
        if best is None or e < best[0] or (e == best[0] and (y + 1) < best[1][0]): best = (e, (y + 1, j))
    return opener, best[1], best[0] - R
def reduced(steps):
    act = sorted(set(i for s in steps for i in s['blockers']))
    idx = {i: n + 1 for n, i in enumerate(act)}
    return (tuple((idx[s['setter']], s['lap']) for s in steps), len(act))
def load_known():
    f = 'lat_known_paths_v1.pkl'
    return pickle.load(open(f, 'rb'))['J2']
def summarise(s, M, K):
    S = dict(n=0, skipped=0, land={}, pair={}, cls={}, word={}, free={}, red={}, newword={}, nomove=[], nomove_n=0, top=[], gt7_n=0, gt7=[],
             viol_oc=[], viol_gate=[], known_n=0, nm_hist={})
    top = []
    for mid in combinations(range(s + 1, M), 5):
        ks = (s,) + mid + (M,)
        g = 0
        for k in ks: g = gcd(g, k)
        if g != 1: S['skipped'] += 1; continue
        rh = [F(k, s) for k in ks]
        steps, R = path(rh)
        opener, closer, width = outcome_from(rh, steps, R)
        w = tuple((x['setter'] + 1, x['lap']) for x in steps); orank = opener[0] if opener else None
        S['n'] += 1
        S['land'].setdefault(R, ks); S['pair'].setdefault((orank, closer[0]), ks); S['cls'].setdefault((orank, closer[0], width), ks)
        S['word'].setdefault(w, ks); S['free'].setdefault(tuple(x[0] for x in w), ks); S['red'].setdefault(reduced(steps), ks)
        if w in K: S['known_n'] += 1
        else: S['newword'].setdefault(w, ks)
        S['nm_hist'][len(w)] = S['nm_hist'].get(len(w), 0) + 1
        if not w:
            S['nomove_n'] += 1
            if len(S['nomove']) < 50: S['nomove'].append(ks)
        if R > 7:
            S['gt7_n'] += 1
            if len(S['gt7']) < 20: S['gt7'].append((R, ks))
        if orank is not None and closer[0] == orank and orank != 7: S['viol_oc'].append(ks)
        if (R > 7) != any(x[0] == 1 for x in w): S['viol_gate'].append(ks)
        top.append((R, ks))
        if len(top) > 4000: top.sort(reverse=True); top = top[:5]
    top.sort(reverse=True); S['top'] = top[:5]
    return S
if __name__ == "__main__":
    s = int(sys.argv[1]); A7 = int(sys.argv[2]); budget = float(sys.argv[3])
    sf = 'lat_state2_s%d_v1.pkl' % s
    st = pickle.load(open(sf, 'rb')) if os.path.exists(sf) else dict(doneM=s + 4, rec={})
    K = load_known(); t0 = time.time()
    while st['doneM'] < A7 and time.time() - t0 < budget:
        M = st['doneM'] + 1
        st['rec'][M] = summarise(s, M, K); st['doneM'] = M
        pickle.dump(st, open(sf + '.tmp', 'wb')); os.replace(sf + '.tmp', sf)
        print('s', s, 'M', M, 'n', st['rec'][M]['n'], 'elapsed %.0f' % (time.time() - t0), flush=True)
    print('doneM', st['doneM'], 'target', A7)
