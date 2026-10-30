"""E654: list frac(delta*) for the landings outside C_j in v2, with an exact pointwise check `clear(delta, j, q)`."""
import math, pickle, importlib.util, io, contextlib
from fractions import Fraction as F
from collections import Counter
spec = importlib.util.spec_from_file_location('m', 'two_block_delta_map_v2.py')
src = open('two_block_delta_map_v2.py').read().split('print("Phase windows')[0]
ns = {}; exec(compile(src, 'x', 'exec'), ns)
Cj, clear, frac = ns['Cj'], ns['clear'], ns['frac']
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
c = Counter()
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0 or op[0] != 'set': continue
    v = sp(p, G + p - 1, b); ownb = list(range(p)) if k < p else list(range(p, 8))
    if op[1] in ownb: continue
    s = b if k < p else F(1)
    oth = [i for _, i in sorted((abs(v[i] - v[k]), i) for i in range(8) if i not in ownb)]
    q = len(oth); j = oth.index(op[1]); f = frac(s * t)
    if any(a <= f <= bb for a, bb in Cj(j, q)): continue
    c[(q, j, str(f), 'pointwise clear' if clear(f, j, q) else 'NOT clear')] += 1
for kk, vv in sorted(c.items(), key=lambda x: -x[1]): print(vv, kk)
