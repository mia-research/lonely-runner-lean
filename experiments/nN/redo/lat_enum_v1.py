# Exhaustive lattice enumeration. usage: lat_enum_v1.py m Nmax [Mlo Mhi]  (k = m*rho, set {m<k2<..<k7<=m*Nmax}; chunk by k7 = M)
# Uses path()/outcome() verbatim (exec'd). State per M is checkpointed in lat_state_m{m}_v1.pkl.
import sys, os, pickle, time
from fractions import Fraction as F
from itertools import combinations
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0].split("exec(open")[0])
exec("\n".join(l for l in open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0].split("\n") if not l.startswith("exec(")))
m = int(sys.argv[1]); Nmax = int(sys.argv[2]); budget = float(sys.argv[3]) if len(sys.argv) > 3 else 500
sf = 'lat_state_m%d_v1.pkl' % m
st = pickle.load(open(sf, 'rb')) if os.path.exists(sf) else dict(doneM=m + 4, rec={})  # rec[M] = per-M summary (dict)
# per-M summary: counts and dicts item->example arrangement (first seen at this M)
def summarise(M):
    S = dict(n=0, land={}, pair={}, cls={}, word={}, free={}, nomove=[], nomove_n=0, top=[], gt7=[], viol_oc=[], viol_gate=[], nm_hist={}, gt7_n=0)
    top = []
    for mid in combinations(range(m + 1, M), 5):
        ks = (m,) + mid + (M,)
        o = outcome([F(k, m) for k in ks])
        R = o['R']; S['n'] += 1
        op = o['opener']; cl = o['closer'][0]; w = o['path']
        orank = op[0] if op else None
        S['land'].setdefault(R, ks)
        S['pair'].setdefault((orank, cl), ks)
        S['cls'].setdefault((orank, cl, o['width']), ks)
        S['word'].setdefault(w, ks)
        S['free'].setdefault(tuple(x[0] for x in w), ks)
        S['nm_hist'][o['nmoves']] = S['nm_hist'].get(o['nmoves'], 0) + 1
        if not w:
            S['nomove_n'] += 1
            if len(S['nomove']) < 50: S['nomove'].append(ks)
        if R > 7:
            S['gt7_n'] += 1
            if len(S['gt7']) < 20: S['gt7'].append((R, ks))
        if orank is not None and cl == orank and orank != 7: S['viol_oc'].append(ks)
        if (R > 7) != any(x[0] == 1 for x in w): S['viol_gate'].append(ks)
        top.append((R, ks)); 
        if len(top) > 4000: top.sort(reverse=True); top = top[:5]
    top.sort(reverse=True); S['top'] = top[:5]
    return S
t0 = time.time()
while st['doneM'] < m * Nmax and time.time() - t0 < budget:
    M = st['doneM'] + 1
    st['rec'][M] = summarise(M); st['doneM'] = M
    pickle.dump(st, open(sf + '.tmp', 'wb')); os.replace(sf + '.tmp', sf)
    print('m', m, 'M', M, 'n', st['rec'][M]['n'], 'elapsed %.0f' % (time.time() - t0), flush=True)
print('doneM', st['doneM'], 'target', m * Nmax)
