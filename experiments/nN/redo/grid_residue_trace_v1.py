"""Owner: trace the six grid residues.  For the slowest runner in Case C (the nearest runner sets the AP scale; the
other six wrap and must land on clear residues mod 8), as the scale D moves down through the nearest runner's range
(u = g_1/D from 1 to 7: the nearest reading r_1 = u stays in the first lap), each wrapped reading's residue
r_j mod 8 = (rho_j u) mod 8 rotates at its own rate rho_j.  Trace the cascade step by step in this picture: at each
cascade instant, every reading's residue in eighths (r mod 8), which are blocked (within 1 of 0 mod 8), and the setter.
Exact.  Arrangements: the five hardest Case C climbs (casec_R_climb_v1) and five Case C sample arrangements with the
most cascade moves."""
import re, io, contextlib
from fractions import Fraction as F
from math import floor
from arrangement_lib import nd

def trace(ds):
    g = ds[0]; t = F(1, 8 * g); rows = []
    while True:
        r = [8 * d * t for d in ds]                    # readings in scale units, D = 1/(8t)
        res = [x % 8 for x in r]
        way = [j for j, d in enumerate(ds) if nd(d * t) < F(1, 8)]
        rows.append((8 * g * t, r, res, way))
        if not way: return rows
        cand = {j: (F(floor(ds[j] * t - F(1, 8)) + 1) + F(1, 8)) / ds[j] for j in way}
        j = max(cand, key=lambda x: cand[x]); rows[-1] = rows[-1] + (j,); t = cand[j]

def show(tag, ds):
    rho = [float(F(d, ds[0])) for d in ds]
    print(f"\n{tag}: readings/g1 {[round(x, 3) for x in rho]}")
    print("   u = r_1   | residues r_j mod 8 of the six wrapped readings (* = blocked, within 1 of 0 mod 8) | setter")
    for row in trace(ds):
        u, r, res, way = row[:4]; s = row[4] if len(row) > 4 else None
        cells = ' '.join(f"{float(res[j]):5.2f}{'*' if j in way else ' '}" for j in range(1, len(ds)))
        print(f"   {float(u):7.4f} | {cells} | {'LONELY' if s is None else s}")

if __name__ == '__main__':
    Vs = []
    for line in open('casec_R_climb_v1.out'):
        m = re.search(r'V (\[[^\]]*\])', line)
        if m: Vs.append(eval(m.group(1)))
    for V in Vs[:5]: show("climb", sorted(v - V[0] for v in V[1:]))
    with contextlib.redirect_stdout(io.StringIO()):
        import case_c_map_v1 as cm
    cm.rnd.seed(26); pool = []
    for shape in ('even', 'clumped+outliers', 'even+clump'):
        for g1div in (30, 100, 1000):
            n = 0
            while n < 150:
                g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
                if g1 + W6 <= 22 * g1: continue
                V = cm.arrangement([g1] + g)
                if len(set(V)) < 8: continue
                n += 1; ds = sorted(v - V[0] for v in V[1:]); pool.append((len(trace(ds)), shape, ds))
    pool.sort(key=lambda x: -x[0])
    for L, shape, ds in pool[:5]: show(f"Case C {shape} ({L - 1} moves)", ds)
