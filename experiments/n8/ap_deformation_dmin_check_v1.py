from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from ap_deformation_series_v1 import arrangement, dist, E8
def dmin(V, i): return min(abs(V[j]-V[i]) for j in range(8) if j != i)
if __name__ == "__main__":
    offs = [F(s)*F(x,100) for x in (1,10,30,50,90) for s in (-1,1)]
    jobs = [({k: e},) for k in range(8) for e in offs] + \
           [({k1: e1, k2: e2},) for k1 in range(8) for k2 in range(k1+1, 8) for e1 in (F(-3,10), F(3,10)) for e2 in (F(-3,10), F(3,10))]
    with Pool(8) as p: res = p.map(arrangement, jobs)
    c = Counter(); lonely_at_pred = Counter(); ex = []
    for r in res:
        if r is None: continue
        V, recs = r
        for x in recs:
            if x["role"] == "moved": continue
            dm1 = dmin(V, x["i"]) == 1
            on = x["phase"] is not None
            c[(f"d_min = 1: {dm1}", f"at AP instant: {on}")] += 1
            if not on:
                lonely_at_pred[x["pred"] is not None] += 1
                if dm1 and len(ex) < 3:
                    ex.append(([str(v) for v in V], x["i"]+1, str(x["t"]), str(x["pred"])))
    print("unmoved runners, E1 + E2:")
    for k in sorted(c): print("  ", k, c[k])
    print("  off-AP unmoved runners that are still lonely at a predicted odd-eighth AP instant:", dict(lonely_at_pred))
    print("  d_min = 1 but framework time is off-AP (it found an EARLIER time), e.g.:", ex)
