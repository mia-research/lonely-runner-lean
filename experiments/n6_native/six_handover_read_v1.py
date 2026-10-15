#!/usr/bin/env python3
"""E28 reader for six_handover_v1.py output. Per death of the isolation box A (mover m):
  (1) closing pair: roles of mover and partner, and whether the partner is A's flank;
  (2) takeover B: Delta = B - A (lap differences), classified as: mover's next lap (e_m, or -e_m when moving down),
      other single-runner steps, multi-runner;
  (3) B's flank relative to the mover (same / slower / faster);
  (4) at B's instant, the readings of A's flank and of the mover (where they sit in their bands);
  (5) for Delta not a single mover step: the full Delta patterns.
Usage: six_handover_read_v1.py file.tsv"""
import sys, ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
for group in ("ordinary", "chain"):
    R = [r for r in rows if r[0] == group]
    roles = Counter(); partner_is_flank = Counter(); delta = Counter(); bflank = Counter(); other = Counter()
    rd_flankA = Counter(); n_open = Counter(); single = Counter()
    for r in R:
        S = ast.literal_eval(r[1]); m = int(r[2]); A = ast.literal_eval(r[4]); fA = ast.literal_eval(r[5])
        cl = ast.literal_eval(r[7]); B = ast.literal_eval(r[8]); fB = ast.literal_eval(r[9])
        rd = [F(x) for x in ast.literal_eval(r[11])]
        for (i, j, ki, kj) in cl:
            role = "mover enters" if i == m else ("mover leaves" if j == m else "mover absent")
            roles[role] += 1
            partner = j if i == m else i
            partner_is_flank[partner in fA] += 1
        d = tuple(b - a for a, b in zip(A, B))
        nz = [(i + 1, x) for i, x in enumerate(d) if x]
        if len(nz) == 1 and nz[0][0] == m: cls = f"mover only, {nz[0][1]:+d}"
        elif len(nz) == 1: cls = "one other runner"
        else: cls = f"{len(nz)} runners" + (" incl. mover" if any(i == m for i, _ in nz) else "")
        delta[cls] += 1
        if not cls.startswith("mover only"): other[tuple(nz)] += 1
        f = fB[0]; bflank["mover" if f == m else ("slower" if f < m else "faster")] += 1
        n_open[min(int(r[12]), 6)] += 1
    print(f"== {group}: deaths of the isolation box {len(R)}")
    print("   closing pair roles:", dict(roles), "; partner is A's flank:", dict(partner_is_flank))
    print("   takeover B - A:", dict(delta.most_common()))
    print("   B's flank relative to the mover:", dict(bflank))
    print("   open boxes at the death point (6 = 6+):", dict(sorted(n_open.items())))
    print("   commonest other Delta (runner, lap change):", other.most_common(10))

# (6) displacement of the instant at each handover, in laps of the mover (x * (tB - tA)) and in readings
print("== displacement and readings")
for group in ("ordinary", "chain"):
    R = [r for r in rows if r[0] == group]
    gap = {}; edge = Counter()
    for r in R:
        m = int(r[2]); x = F(r[3]); A = ast.literal_eval(r[4]); B = ast.literal_eval(r[8])
        tA, tB = F(r[6]), F(r[10]); d = tuple(b - a for a, b in zip(A, B))
        nz = [(i + 1, v) for i, v in enumerate(d) if v]
        cls = "mover only" if (len(nz) == 1 and nz[0][0] == m) else "other"
        g = x * (tB - tA); gap.setdefault(cls, Counter())[g if cls == "mover only" else round(float(g), 2)] += 1
        rd = [F(v) for v in ast.literal_eval(r[11])]
        if cls == "other":
            fB = ast.literal_eval(r[9])[0]
            # where the mover sits at B's instant, and the slack of every runner (distance to its nearer edge)
            edge[("mover reading", str(rd[m - 1]) if rd[m - 1] in (F(1, 6), F(5, 6)) else ("in band" if F(1, 6) < rd[m - 1] < F(5, 6) else "?"))] += 1
    for cls, c in gap.items():
        print(f"   {group} {cls}: mover-laps from A's instant to B's: {dict(c.most_common(8))}")
    print(f"   {group} other: {dict(edge)}")

# (7) multi-step handovers: who is in the way at the mover's next entry (the single-step candidate)
print("== who blocks the mover's next entry, when the takeover is later")
def cdist(z):
    f = z - (z.numerator // z.denominator); return min(f, 1 - f)
for group in ("ordinary", "chain"):
    R = [r for r in rows if r[0] == group]
    blk = Counter(); blkset = Counter(); fBrel = Counter()
    for r in R:
        S = ast.literal_eval(r[1]); m = int(r[2]); x = F(r[3]); A = ast.literal_eval(r[4])
        tB = F(r[10]); W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x
        t1 = F(6 * (A[m - 1] + 1) + 1, 6) / x
        if tB == t1: continue
        inway = tuple(i + 1 for i in range(5) if cdist(W[i] * t1) < F(1, 6))
        blkset[tuple("slower" if i < m else ("mover" if i == m else "faster") for i in inway)] += 1
        for i in inway: blk["slower" if i < m else "faster"] += 1
        fB = ast.literal_eval(r[9])[0]
        fBrel[("B flank in the way at t1" if fB in inway else "B flank not in the way at t1")] += 1
    print(f"   {group}: blockers at the mover's next entry: {dict(blk)}; patterns {dict(blkset.most_common(6))}; {dict(fBrel)}")

# (8) was the takeover box already open before the death, or born at it?
print("== takeover already open before the death?")
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns); alive_interval = ns["alive_interval"]
for group in ("ordinary", "chain"):
    R = [r for r in rows if r[0] == group]
    c = Counter()
    for r in R:
        S = ast.literal_eval(r[1]); m = int(r[2]); x = F(r[3]); B = ast.literal_eval(r[8])
        V = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]
        lo, hi = alive_interval(V, m - 1, B)
        start = S[0] * m; up = F(S[m - 1]) > start
        c["already open" if (lo < x if up else hi > x) else "born at the death point"] += 1
    print(f"   {group}: {dict(c)}")
