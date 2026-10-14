import csv
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
def fr(x): return x - floor(x)
def signed8(x): x = fr(x); return 8 * (x if x <= F(1, 2) else x - 1)
rows = list(csv.DictReader(open("out_full_transit_positions_v2.csv")))
conf = defaultdict(dict)
for r in rows: conf[(int(r["mover"]), r["r"])][int(r["runner"])] = r
AP = [F(k) for k in range(1, 9)]
c = Counter(); band = Counter()
for (m, rv), R in conf.items():
    V = list(AP); V[m - 1] = F(rv); dev = V[m - 1] - AP[m - 1]
    if dev == 0: continue
    nb = m + 1 if dev > 0 else m - 1
    if nb in (0, 9): continue
    i = m - 1; gap = abs(V[i] - V[nb - 1]); tc = 1 / (8 * gap)
    shared = R[m]["t"] == R[nb]["t"] and F(R[m]["t"]) == tc
    inway = {j for j in range(8) if j != i and abs(signed8((V[j] - V[i]) * tc)) < 1}
    # band identity at the pair's own scale: reading s = |v_j - v_i| / gap is in the way at u = 1/8 iff |s - 8N| < 1
    pred = {j for j in range(8) if j != i and any(abs(abs(V[j] - V[i]) / gap - 8 * N) < 1 for N in range(0, 200))}
    band["band identity at the pair scale predicts who is in the way"] += pred == inway
    band["no runner in the way  <=>  pair shares the spine point"] += (not inway) == shared or (not inway and R[nb]["t"] != R[m]["t"])
    if shared or not inway: continue
    t = F(R[m]["t"])
    at8 = {j for j in range(8) if j != i and abs(signed8((V[j] - V[i]) * t)) == 1}
    c["cases with a runner in the way at the spine point"] += 1
    c["a runner in the way there is at exactly 1/8 at the actual time"] += bool(inway & at8)
    c["actual time later than the spine point"] += t > tc
print(dict(band)); print(dict(c))
