"""E647 analysis of two_block_strip_cascade_v1.pkl: outcome of each (arrangement, subject) by the place it lands.
Roles relative to the subject k: 'own' = opener in the subject's block, 'other' = in the other block; 'edgeO' = the
other block's runner nearest the subject's block, 'dmin' = the subject's nearest runner. Exact."""
import pickle
from fractions import Fraction as F
from collections import Counter
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def block(p, i): return 0 if i < p else 1
out = Counter(); bypk = Counter(); maxR = F(0); maxM = 0; maxmv = 0; arg = None
lapC = Counter(); Rbins = Counter()
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    kind, i = op
    bk = block(p, k); bi = block(p, i)
    edge_other = (p - 1) if bk == 1 else p  # nearest runner of the other block to the subject's block
    tag = []
    if kind == 'start': tag.append('bound 1/(8dmin)')
    else:
        tag.append('own' if bi == bk else 'other')
        if bi != bk and i == edge_other: tag.append('edge')
        tag.append('lap%d' % M if M <= 3 else 'lap>3')
    key = (('interleaved' if G <= 0 else 'gap'),) + tuple(tag)
    out[key] += 1
    lapC[M] += 1
    if R > maxR: maxR = R; arg = (p, b, G, k, t, op, M, mv)
    maxmv = max(maxmv, mv); maxM = max(maxM, M)
    Rbins[('R<=7' if R <= 7 else 'R in (7,9)' if R < 9 else 'R>=9')] += 1
print("records:", len(recs))
for kk, vv in sorted(out.items(), key=lambda x: -x[1]): print("  ", vv, kk)
print("lap histogram:", sorted(lapC.items())[:20], " max lap:", maxM, " max moves:", maxmv)
print("R bins:", dict(Rbins), " max R:", maxR, float(maxR), " at", arg)
