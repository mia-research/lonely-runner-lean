# taxo_tie_v1.py -- exit ties at the landing: zones (y,j) with (8j+1)/rho_y == R*.  Compare cascade opener with
# variant B (among zones with exit R*: smallest entry, then highest rank) and variant A (highest rank), on every sample row with nm>=1.
import pickle
from fractions import Fraction as F
from collections import Counter
rows = pickle.load(open('taxo_sample_v1.pkl', 'rb'))
tied = 0; A_bad = []; B_bad = []; nested_bad = 0
for r in rows:
    name, rho, lab, lab2, okR, nm, op, cl, w, R = r
    if nm == 0: continue
    zs = [(y, int((R * rho[y] - 1) / 8)) for y in range(7) if (R * rho[y] - 1) % 8 == 0 and R * rho[y] > 1]
    if len(zs) < 2: continue
    tied += 1
    A = max(zs); B = min(zs, key=lambda z: (F(8 * z[1] - 1) / rho[z[0]], -z[0]))
    if (A[0] + 1, A[1]) != op: A_bad.append((rho, op, A))
    if (B[0] + 1, B[1]) != op: B_bad.append((rho, op, B))
print("rows with nm>=1 and an exit tie at the landing:", tied)
print("variant A (highest rank among tied zones) disagrees with cascade opener:", len(A_bad))
print("variant B (smallest entry, then highest rank) disagrees with cascade opener:", len(B_bad))
for x in B_bad[:5]: print("  ", [str(t) for t in x[0]], "cascade", x[1], "B", (x[2][0] + 1, x[2][1]))
