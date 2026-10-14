"""Exact cascade for the AP-neighbourhood counterexample of Fresh/APNeighbourhood.lean (cxE): speeds c + j + e_j with
e_0 = 1/15, e_1 = -1/15, e_7 = 1/15, others 0, c = 1.  Subject runner 1.  Exact Fractions."""
from fractions import Fraction as F
from math import floor
c = F(1); e = [F(1,15), F(-1,15), 0, 0, 0, 0, 0, F(1,15)]
v = [c + j + e[j] for j in range(8)]; k = 1
ds = sorted(abs(v[i] - v[k]) for i in range(8) if i != k)
def inway(d, t):
    x = d*t; return abs(x - floor(x + F(1,2))) < F(1,8)
t = F(1, 8*ds[0]); print("d_min =", ds[0], " start t0 =", t, "(apT?)", F(15,104))
seq = [t]; setters = []
while True:
    blk = [d for d in ds if inway(d, t)]
    if not blk: break
    best = max(((floor(d*t + F(1,2)) + F(1,8))/d, d) for d in blk)
    t = best[0]; seq.append(t); setters.append(best[1])
print("states:", [str(x) for x in seq]); print("setters:", [str(x) for x in setters])
print("landing:", t, " lonely there:", all(not inway(d, t) for d in ds), " equals 135/488:", t == F(135,488))
print("named instant 15/104 lonely:", all(not inway(d, F(15,104)) for d in ds))
