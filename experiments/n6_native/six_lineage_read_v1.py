#!/usr/bin/env python3
"""E30 reader for six_lineage_v1.py: per group, deaths of the followed box; takeover status (open before / born at
the death); B - L classified (one runner +-1 lap, one runner +-more, several runners); jump sign and size in 1/d_min;
for born takeovers, the closing and opening pairs and the double-coincidence test: mover m laps a (exit) / a+1
(entry) against runner p laps b (entry) / b' (exit) at one ratio r = d_p/x, i.e.
(6b+1)/(6a+5) = (6b'+5)/(6a+7) = r. Usage: six_lineage_read_v1.py file.tsv"""
import sys, ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
for grp in ("ordinary", "chain"):
    R = [r for r in rows if r[0].startswith(grp)]
    paths = Counter(r[0] for r in R)
    status = Counter(); dcls = Counter(); sign = Counter(); size = Counter(); born = []; nal = Counter(); dpat = Counter()
    for r in R:
        d = ast.literal_eval(r[6]); nz = [(i + 1, v) for i, v in enumerate(d) if v]
        if len(nz) == 1: cls = f"one runner {'+' if nz[0][1] > 0 else '-'}{abs(nz[0][1])}"
        else: cls = f"{len(nz)} runners"
        dcls[cls] += 1; dpat[tuple(nz)] += 1
        j = F(r[7]); sign["later" if j > 0 else ("earlier" if j < 0 else "same instant")] += 1
        size[min(round(abs(float(r[8])), 1), 2.0)] += 1
        status[r[10]] += 1; nal[min(int(r[12]), 10)] += 1
        if r[10] == "born": born.append(r)
    print(f"== {grp}: paths with a lineage death {len(paths)}; deaths {len(R)}; max deaths on one path {max(paths.values()) if paths else 0}")
    print("   takeover status:", dict(status))
    print("   B - L:", dict(dcls.most_common()))
    print("   commonest B - L (runner, laps):", dpat.most_common(8))
    print("   jump direction:", dict(sign), "; |jump| in 1/d_min (2.0 = 2+):", dict(sorted(size.items())))
    print("   boxes alive just past the death (10 = 10+):", dict(sorted(nal.items())))
    ok = Counter(); ex = []
    for r in born:
        m = int(r[1]); x = F(r[2]); L = ast.literal_eval(r[3]); B = ast.literal_eval(r[5])
        cl = ast.literal_eval(r[4]); op = ast.literal_eval(r[11])
        hit = False
        for (p, mm, b, a) in cl:
            if mm != m: continue
            for (mm2, p2, a1, b2) in op:
                if mm2 == m and p2 == p and a1 == a + 1:
                    r1, r2 = F(6*b + 1, 6*a + 5), F(6*b2 + 5, 6*a + 7)
                    if r1 == r2: hit = True; ex.append((m, p, a, b, b2, r1))
        ok[hit] += 1
    print("   born takeovers:", len(born), "; double coincidence (mirror pair at one ratio):", dict(ok))
    print("   (mover, p, a, b, b', r):", Counter(ex).most_common(10))
