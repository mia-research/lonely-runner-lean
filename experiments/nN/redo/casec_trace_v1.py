"""Owner: every arrangement resolves exactly -- use the cascade to see what is going on at the top of the Case C R climb
(casec_R_climb_v1).  For each of the five highest climbed arrangements, trace the cascade of the slowest runner from
R = 1 step by step: at each instant R, every runner's position (fraction of its lap, 0 = the subject's slot), which
are in the way (within 1/8), and the setter (the latest exit).  Exact; positions printed to 3 places."""
import re
from fractions import Fraction as F
from math import floor
from arrangement_lib import nd

def trace(V):
    ds = sorted(v - V[0] for v in V[1:]); g = ds[0]; t = F(1, 8 * g); rows = []
    while True:
        pos = [(d * t) % 1 for d in ds]
        way = [j for j, d in enumerate(ds) if nd(d * t) < F(1, 8)]
        rows.append((8 * g * t, pos, way))
        if not way: return ds, rows
        cand = {j: (F(floor(ds[j] * t - F(1, 8)) + 1) + F(1, 8)) / ds[j] for j in way}
        j = max(cand, key=lambda x: cand[x]); rows[-1] = rows[-1] + (j,); t = cand[j]

if __name__ == '__main__':
    Vs = []
    for line in open('casec_R_climb_v1.out'):
        m = re.search(r'V (\[[^\]]*\])', line)
        if m: Vs.append(eval(m.group(1)))
    for V in Vs[:5]:
        ds, rows = trace(V)
        print(f"\nV {V}  readings/g1 {[round(float(F(d, ds[0])), 4) for d in ds]}")
        for r in rows:
            R, pos, way = r[:3]; setter = r[3] if len(r) > 3 else None
            ps = ' '.join(f"{float(p):.3f}{'*' if j in way else ' '}" for j, p in enumerate(pos))
            print(f"  R {float(R):7.4f}  positions [{ps}]  " + (f"setter {setter}" if setter is not None else "LONELY"))
