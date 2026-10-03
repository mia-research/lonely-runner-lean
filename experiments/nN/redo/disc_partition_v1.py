# (4) Groups by outcome, exact.  closer = the reading minimising (7-p_y)/rho_y ; opener = last setter (at p=1).
import pickle
from fractions import Fraction as F
from collections import Counter
rec = pickle.load(open('disc_records_v1.pkl', 'rb'))
G = {}
for r in rec:
    op = r[6][-1][0]+1; q = [(7-p)/x for p, x in zip(r[4], r[1])]; m = min(q); cs = [i+1 for i, v in enumerate(q) if v == m]; c = cs[0]
    if any(y == 0 for y, j in r[6]): g = 'G1 reading 1 sets a move (state 9; R*>=9)'
    elif c == op: g = 'G4 closer == opener'
    elif c < op: g = 'G2 closer rank < opener rank'
    else: g = 'G3 closer rank > opener rank'
    G.setdefault(g, []).append((r, op, c, len(cs)))
for g in sorted(G):
    L = G[g]; rs = [x[0][2] for x in L]; nm = [len(x[0][6]) for x in L]
    print("%s : %d members ; R* in [%.6f, %.6f] ; moves in [%d,%d] ; opener ranks %s ; closer ranks %s ; members with 2 tied closers %d ; with a p==1 tie %d ; with p==7 %d" % (g, len(L), float(min(rs)), float(max(rs)), min(nm), max(nm), sorted(Counter(x[1] for x in L).items()), sorted(Counter(x[2] for x in L).items()), sum(1 for x in L if x[3] > 1), sum(1 for x in L if sum(1 for p in x[0][4] if p == 1) > 1), sum(1 for x in L if any(p == 7 for p in x[0][4]))))
# the proof that closer==opener needs rank 7: reading 7 has (7-p_7)/rho_7 <= 6/rho_7 < 6/rho_k
bad = sum(1 for r in rec if r[6][-1][0] < 6 and (7-r[4][6])/r[1][6] >= 6/r[1][r[6][-1][0]])
print("members whose opener rank k<7 has (7-p_7)/rho_7 >= 6/rho_k (would contradict the inequality): %d" % bad)
# G1 internal: laps of exit after 9
print("G1: state after 9 exists (R*>9) in %d ; R*==9 in %d" % (sum(1 for x in G['G1 reading 1 sets a move (state 9; R*>=9)'] if x[0][2] > 9), sum(1 for x in G['G1 reading 1 sets a move (state 9; R*>=9)'] if x[0][2] == 9)))
