# E643: for the 10 survivors not covered by m*core, does some 6-subset admit a real-y certificate (the chain of gen_real_core_v1.cert)?  Exact.
import sys, itertools, math
sys.argv = ['x']
from fractions import Fraction as F
from gen_real_core_v1 import cert
rest = [(1,4,28,30,31,32,38),(1,6,29,30,31,32,35),(1,7,8,15,22,23,30),(1,8,33,35,36,37,41),(1,8,33,35,36,37,42),(1,13,14,15,16,29,36),(1,13,14,15,16,29,42),(1,13,16,28,29,30,33),(1,16,27,29,30,31,35),(1,28,29,30,32,35,39)]
newcores = {}
for S in rest:
    found = []
    for sub in itertools.combinations(S, 6):
        try: c = cert(sub)
        except Exception as e: c = None
        if c: found.append((sub, len(c['chain']), c['y0']))
    print(S, 'subsets with a real-y certificate:', [(s, n, str(y0)) for s, n, y0 in found][:4], 'count', len(found), flush=True)
    for s, n, y0 in found: newcores[s] = (n, y0)
print('distinct cores found', len(newcores))
import pickle; pickle.dump(newcores, open('survivor_cores_v1.pkl', 'wb'))
