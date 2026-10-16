#!/usr/bin/env python3
"""Toward a hand-symbolic §8. (1) The four closed-form cases A (first window x4(5-x3) >= 4x3), B (four-block fold
x4 <= 5, x5(5-x4) >= 2x4), C (spread box x5 <= 5), D (second-lap box x4 <= 5, 7x4 <= 5x5, x5 <= 11): which certificate
leaves (S8CertFull_v1's tree, rebuilt) lie wholly inside A or B or C or D (checked at the leaf's worst corner) and which
lie in the remainder R. (2) For R: the statements its leaves use, and a merge of same-statement leaves into larger boxes
(two boxes merge when they agree on three sides and abut on the fourth), giving the number of cases a hand proof of R
would have with the present statements."""
import sys
from fractions import Fraction as F
from collections import Counter
sys.setrecursionlimit(100000)
exec(open("s8_cert_lean_gen_v2.py").read().split("def q(x)")[0])
leaves = []
def walk(t, c):
    cc = clip(c)
    if t[0] == "none": return
    if t[0] == "leaf": leaves.append((cc, t[1])); return
    _, d, mid, l, r = t
    walk(l, setHi(cc, d, mid)); walk(r, setLo(cc, d, mid))
walk(tree, root)
def caseA(c):  # x4(5 - x3) >= 4 x3 at worst corner: x4 lo, x3 hi
    lo, hi = c; return lo[2] * (5 - hi[1]) >= 4 * hi[1]
def caseB(c):
    lo, hi = c; return hi[2] != 0 and hi[2] <= 5 and lo[3] * (5 - hi[2]) >= 2 * hi[2]
def caseC(c): lo, hi = c; return hi[3] != 0 and hi[3] <= 5
def caseD(c): lo, hi = c; return hi[3] != 0 and hi[2] <= 5 and 7 * hi[2] <= 5 * lo[3] and hi[3] <= 11
cnt = Counter(); R = []
for c, r in leaves:
    k = "A" if caseA(c) else "B" if caseB(c) else "C" if caseC(c) else "D" if caseD(c) else "R"
    cnt[k] += 1
    if k == "R": R.append((c, (r[0], r[1])))
print("leaves", len(leaves), "by case (wholly inside):", dict(cnt))
print("statements used in R:", Counter(s for _, s in R).most_common())
boxes = [(list(map(list, c)), s) for c, s in R]
changed = True
while changed:
    changed = False
    for i in range(len(boxes)):
        for j in range(i + 1, len(boxes)):
            (ci, si), (cj, sj) = boxes[i], boxes[j]
            if si != sj: continue
            diff = [d for d in range(4) if (ci[0][d], ci[1][d]) != (cj[0][d], cj[1][d])]
            if len(diff) == 1:
                d = diff[0]
                if ci[1][d] == cj[0][d] or cj[1][d] == ci[0][d]:
                    lo = min(ci[0][d], cj[0][d]); hi = max(ci[1][d], cj[1][d]) if 0 not in (ci[1][d], cj[1][d]) else 0
                    ci[0][d], ci[1][d] = lo, hi; boxes.pop(j); changed = True; break
        if changed: break
print("R after merging same-statement neighbours:", len(boxes), "boxes")
