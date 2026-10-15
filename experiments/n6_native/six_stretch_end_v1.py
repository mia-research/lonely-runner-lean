#!/usr/bin/env python3
"""E33: why J (the four others' common stretch) reaches past r's next entry when the lap-k piece dies, at the
lineage neighbour takeovers (six_lineage_v1.tsv, takeover = L +- e_r). Speeds exactly at the death x.
J = [J0, J1]: J0 = entry of runner p (J's latest entry, lap k_p), J1 = exit of runner q (J's earliest exit, lap k_q).
At the instant J0 (p's opening k_p) runner q reads rho_q = frac(d_q * J0); in the framework's residue form at p's
opening, rho_q = (d_q (6 k_p + 1) mod 6 d_p) / (6 d_p). J's length = (5/6 - rho_q)/d_q. Takeover (NeighbourCut
`takeover_open`) needs e_{k+1} < J1; when the lap-k piece dies at r's exit (x_k = J0), that is
    5/6 - rho_q  >  d_q / (3 d_r)          ("q's remaining clear time beats r's blocked window").
Records per death: how the piece died (r's exit at J0, or other), roles of p, q, r, rho_q, the two sides of the
inequality, and which side carries it. Usage: six_stretch_end_v1.py file.tsv"""
import sys, ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
def frac(z): return z - (z.numerator // z.denominator)
died = Counter(); roles = Counter(); rho = Counter(); win = Counter(); side = Counter(); marg = Counter(); n = 0
same = Counter(); ex = []
for row in rows:
    d = ast.literal_eval(row[6]); nz = [(i + 1, v) for i, v in enumerate(d) if v]
    if len(nz) != 1 or abs(nz[0][1]) != 1: continue
    r, s = nz[0]; n += 1
    S = ast.literal_eval(row[0][row[0].index("("):]); m = int(row[1]); x = F(row[2]); L = ast.literal_eval(row[3])
    W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x
    others = [i for i in range(1, 6) if i != r]
    ent = {i: (6 * L[i-1] + 1) / (6 * W[i-1]) for i in others}; ext = {i: (6 * L[i-1] + 5) / (6 * W[i-1]) for i in others}
    J0, J1 = max(ent.values()), min(ext.values())
    p = [i for i in others if ent[i] == J0][0]; q = [i for i in others if ext[i] == J1][0]
    dr = W[r-1]; kr = L[r-1]
    # which of r's bands is L's, and which is the takeover's
    xk = (6 * kr + 5) / (6 * dr); ek = (6 * kr + 1) / (6 * dr)
    if s == 1: how = "r's exit meets J's start" if xk == J0 else ("J's end meets r's entry" if J1 == ek else "other")
    else:      how = "r's entry meets J's end" if ek == J1 else ("J's start meets r's exit" if J0 == xk else "other")
    died[(f"takeover r lap {'+1' if s == 1 else '-1'}", how)] += 1
    def rl(i): return "M" if i == m else ("slower" if i < m else "faster")
    roles[(rl(p), rl(q), "r=" + rl(r))] += 1
    rq = frac(W[q-1] * J0)
    rho[round(float(rq), 2)] += 1
    lhs = F(5, 6) - rq; rhs = W[q-1] / (3 * dr)
    if s == 1 and how == "r's exit meets J's start":
        win[lhs > rhs] += 1
        side["q has >= 1/3 of a lap left (holds even if d_r = d_q)" if lhs >= F(1, 3) else "needs r faster than q"] += 1
        marg[min(round(float(dr / W[q-1]), 0), 10)] += 1
        same[p == q] += 1
print(f"neighbour takeovers: {n}")
print("  how the dying piece died:", dict(died.most_common()))
print("  roles (J's start p, J's end q, cutter r):", dict(roles.most_common(8)))
print("  q's reading at J's start (rho_q):", dict(sorted(rho.items(), key=lambda kv: -kv[1])[:12]))
print("  for deaths at r's exit meeting J's start, with takeover on r's next lap:")
print("    5/6 - rho_q > d_q/(3 d_r) holds:", dict(win))
print("    which side carries it:", dict(side))
print("    d_r / d_q (10 = 10+):", dict(sorted(marg.items())))
print("    p == q:", dict(same))
