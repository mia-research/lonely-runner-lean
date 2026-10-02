# taxo_lemma_v1.py -- checks of the K2a emptiness argument on the stored sample.
import pickle
from fractions import Fraction as F
rows = pickle.load(open('taxo_sample_v1.pkl', 'rb'))
def blocks_at_1(r): return any(8 * j - 1 < r < 8 * j + 1 for j in range(1, int(r // 8) + 3))
n2 = [r for r in rows if r[5] >= 2]
a = [r for r in n2 if blocks_at_1(r[1][r[6][0] - 1]) and r[6][1] == round(r[1][r[6][0]-1] / 8)]
print("nm>=2 rows:", len(n2), "| rows whose opener (s,j) is a zone containing R=1 (same lap j = round(rho_s/8)):", len(a))
b = [r for r in rows if r[5] >= 1 and r[6][1] == 1 and blocks_at_1(r[1][r[6][0] - 1]) and r[5] >= 2]
print("nm>=2 with lap-1 strip opener (K2a plus its ties):", len(b))
c = [r for r in rows if r[5] >= 1 and r[6][1] == 1 and r[1][r[6][0]-1] > 7]
print("rows nm>=1 with opener lap 1 and rho_s>7:", len(c), "of which nm>=2:", sum(r[5] >= 2 for r in c))
d = [r for r in rows if r[5] >= 2 and r[6][1] == 1]
print("nm>=2 with opener lap 1:", len(d), "; min rho_s among them:", min(r[1][r[6][0]-1] for r in d), "; max:", max(r[1][r[6][0]-1] for r in d))
