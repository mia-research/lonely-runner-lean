# carve_run_v1.py DATASET [start end] -> carve_rec_DATASET_start_v1.pkl ; records exact checks per member.  single process.
import sys, pickle, random, itertools, time
from math import gcd
from functools import reduce
exec(open('carve_lib_v1.py').read())
def load(name):
    if name == 'J1': return [(i, r) for i, r in pickle.load(open('cell_members7_J1.pkl', 'rb'))]
    if name == 'J2s':
        L = pickle.load(open('cell_members7_J2.pkl', 'rb')); rnd = random.Random(20261004)
        idx = sorted(rnd.sample(range(len(L)), 20000)); return [L[i] for i in idx]
    if name == 'taxo': return [(i, t[1]) for i, t in enumerate(pickle.load(open('taxo_sample_v1.pkl', 'rb')))]
    if name.startswith('lat'):          # lat<s>_<N>: sets s<a2<..<a7<=N, gcd 1, readings a/s
        s, N = name[3:].split('_'); s = int(s); N = int(N); out = []
        for c in itertools.combinations(range(s + 1, N + 1), 6):
            a = (s,) + c
            if reduce(gcd, a) != 1: continue
            out.append((a, [F(x, s) for x in a]))
        return out
name = sys.argv[1]; D = load(name)
st = int(sys.argv[2]) if len(sys.argv) > 2 else 0; en = int(sys.argv[3]) if len(sys.argv) > 3 else len(D)
rnd = random.Random(77); recs = []; t0 = time.time(); bad = 0
for i in range(st, min(en, len(D))):
    idx, rh = D[i]
    d = checks(rh, rnd); d['idx'] = idx; d['rho7'] = sorted(rh)[6]
    if not (d['order_ok'] and d['cc_ok'] and d['landing_ok'] and d['k6_ok'] and (d['gate_cond'] == d['crosser'])): bad += 1
    if d['crosser'] != d['gate_cond'] or not d['W'] and d['crosser']: pass
    recs.append(d)
    if time.time() - t0 > 540: print('TIME STOP at', i); break
pickle.dump(recs, open('carve_rec_%s_%d_v1.pkl' % (name, st), 'wb'))
print(name, 'n', len(recs), 'range', st, i, 'check failures', bad, 'time %.0f' % (time.time() - t0))
