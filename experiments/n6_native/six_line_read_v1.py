#!/usr/bin/env python3
"""E34 readouts on straight-line lineage (six_lineage_line_v1.tsv): the E30 lineage summary, the E31 neighbour
structure (read just before the death), and the E33 stretch-end condition, with speeds d(l) = G + l (S - G).
Roles are by speed rank relative to the cutting runner r (no single mover on these paths)."""
import sys, ast, math
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
def frac(z): return z - (z.numerator // z.denominator)
def speeds(tag, l):
    S = ast.literal_eval(tag[tag.index("("):]); G = [F(S[0] * i) for i in range(1, 6)]
    return [g + l * (F(s) - g) for g, s in zip(G, S)]
for grp in ("ordinary", "chain"):
    R = [r for r in rows if r[0].startswith(grp)]
    # E30
    dcls = Counter(); dpat = Counter(); size = Counter(); sign = Counter(); born = []
    for r in R:
        d = ast.literal_eval(r[5]); nz = [(i + 1, v) for i, v in enumerate(d) if v]
        dcls["one runner %+d" % nz[0][1] if len(nz) == 1 else f"{len(nz)} runners"] += 1; dpat[tuple(nz)] += 1
        j = F(r[6]); sign["later" if j > 0 else "earlier"] += 1; size[min(round(abs(float(r[7])), 1), 2.0)] += 1
        if r[8] == "born": born.append(r)
    print(f"== {grp}: deaths {len(R)} on {len(set(r[0] for r in R))} paths; thin {sum(1 for r in R if r[11] == 'THIN')}")
    print("   B - L:", dict(dcls.most_common()), "; commonest:", dpat.most_common(5))
    print("   jump:", dict(sign), "; |jump| in 1/d_min:", dict(sorted(size.items())))
    br = Counter()
    for r in born:
        W = speeds(r[0], F(r[1])); cl = ast.literal_eval(r[3]); op = ast.literal_eval(r[9])
        br[(tuple(sorted({str(W[j-1] / W[i-1]) for i, j, _, _ in cl})), tuple(sorted({str(W[j-1] / W[i-1]) for i, j, _, _ in op})))] += 1
    print("   born takeovers:", len(born), "; speed ratios in closing / opening pairs:", br.most_common(6))
    # E31 and E33 on single-runner neighbours
    fam = Counter(); fast = Counter(); bnd = Counter(); res = Counter(); carry = Counter(); vals = Counter(); n = 0
    for r in R:
        d = ast.literal_eval(r[5]); nz = [(i + 1, v) for i, v in enumerate(d) if v]
        if len(nz) != 1 or abs(nz[0][1]) != 1: continue
        rr, s = nz[0]; n += 1; L = ast.literal_eval(r[2]); l = F(r[1])
        others = [i for i in range(1, 6) if i != rr]
        for when, W in (("before", speeds(r[0], l - F(1, 10**6))), ("at", speeds(r[0], l))):
            ent = {i: (6*L[i-1]+1) / (6*W[i-1]) for i in others}; ext = {i: (6*L[i-1]+5) / (6*W[i-1]) for i in others}
            J0, J1 = max(ent.values()), min(ext.values()); dr = W[rr-1]
            p = [i for i in others if ent[i] == J0][0]; q = [i for i in others if ext[i] == J1][0]
            if when == "before":
                if J1 > J0:
                    k0 = math.floor(J0 * dr - F(5, 6)); c = 0; kk = k0
                    while (6*kk+1) / (6*dr) < J1:
                        if max(J0, (6*kk+1)/(6*dr)) < min(J1, (6*kk+5)/(6*dr)): c += 1
                        kk += 1
                    fam[min(c, 6)] += 1
                fast["r fastest" if dr == max(W) else f"r rank {sorted(W).index(dr) + 1}"] += 1
                bnd[tuple("slower than r" if W[i-1] < dr else "faster than r" for i in (p, q))] += 1
            else:
                if s == 1: v = frac(W[q-1] * J0); lhs, rhs, bs = F(5, 6) - v, W[q-1] / (3*dr), W[q-1]
                else: v = frac(W[p-1] * J1); lhs, rhs, bs = v - F(1, 6), W[p-1] / (3*dr), W[p-1]
                res[(s, "strict" if lhs > rhs else ("equality" if lhs == rhs else "fails"))] += 1
                carry["binding runner has >= 1/3 lap left" if lhs >= F(1, 3) else "needs r faster than binding runner"] += 1
                vals[(str(v), str(bs / dr))] += 1
    print(f"   neighbour takeovers (one runner +-1): {n}")
    print("     r:", dict(fast.most_common()), "; J bounded by (start, end):", dict(bnd.most_common()))
    print("     r's bands meeting J just before the death:", dict(sorted(fam.items())))
    print("     takeover condition:", dict(sorted(res.items())), "; carried by:", dict(carry))
    print("     commonest (binding reading, binding speed / d_r):", vals.most_common(6))
