"""How much of Case C do the PROVED nested windows (SplitChainN.nested / lonely_of_split) close with the event inside
the nearer neighbour's first band (the neighbour bound), exactly?  In units of g_1 (u = g_1 t), readings rho_1 = 1 < ...
< rho_7, rho_7 > 24.  Two forms:
 (A) core = the readings <= 7 (prefix rho_1..rho_c): clear on [1/8, 7/(8 rho_c)] (every c u in [1/8, 7/8]); the rest,
     as a list slowest first, must be Valid with needT <= 7/(8 rho_c) - 1/8.
 (B) core = {rho_1}: clear on [1/8, 7/8]; the other six, slowest first, Valid with needT <= 3/4.
needT(a :: L) = 2 needT(L) + 1/(4a), Valid: a * needT(L) <= 3/4 at every step (SplitChainN).  Data: the 1,350 Case C
arrangements of E56 and the 179 adversarial climbs of casec_R_climb_v1 (their end points)."""
from fractions import Fraction as F
import io, contextlib, re

def needT(L):
    n = F(0); ok = True
    for a in reversed(L):
        if a * n > F(3, 4): ok = False
        n = 2 * n + 1 / (4 * a)
    return n, ok

def covered(rho):
    core = [r for r in rho if r <= 7]; fast = [r for r in rho if r > 7]
    c = max(core)
    nA, okA = needT(fast); A = okA and nA <= F(7, 8) / c - F(1, 8)
    nB, okB = needT(rho[1:]); B = okB and nB <= F(3, 4)
    return A, B, len(fast)

with contextlib.redirect_stdout(io.StringIO()):
    import case_c_map_v1 as cm
cm.rnd.seed(26); data = []
for shape in ('even', 'clumped+outliers', 'even+clump'):
    for g1div in (30, 100, 1000):
        n = 0
        while n < 150:
            g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
            if g1 + W6 <= 22 * g1: continue
            V = cm.arrangement([g1] + g)
            if len(set(V)) < 8: continue
            n += 1
            ds = sorted(v - V[0] for v in V[1:])
            if ds[-1] > 24 * ds[0]: data.append((shape, [F(d, ds[0]) for d in ds]))
for line in open('casec_R_climb_v1.out'):
    m = re.search(r'V (\[[^\]]*\])', line)
    if m:
        V = eval(m.group(1)); ds = sorted(v - V[0] for v in V[1:]); data.append(('climb', [F(d, ds[0]) for d in ds]))
from collections import Counter
tot = Counter(); A = Counter(); B = Counter(); AB = Counter(); nf = Counter()
for shape, rho in data:
    a, b, k = covered(rho); tot[shape] += 1; A[shape] += a; B[shape] += b; AB[shape] += (a or b); nf[(shape, k)] += 1
for s in tot:
    print(f"{s:17s} {tot[s]:5d}: closed by (A) core <= 7 {A[s]:5d}, by (B) core {{g_1}} {B[s]:5d}, by either {AB[s]:5d}")
print("number of readings above 7 g_1, by family:", sorted(nf.items()))
