#!/usr/bin/env python3
"""Observation: for the failing cells of s8_cert_v3, the lonely lap vectors (boxes and their widths) at each cell's
centre, so the list can be extended. Reads the FAIL lines of s8_cert_v3.out."""
import re
from fractions import Fraction as F
from collections import Counter
cells = []
for l in open("s8_cert_v3.out"):
    if l.strip().startswith("FAIL"):
        cells.append([tuple(F(x) for x in p) for p in re.findall(r"\('([^']+)', '([^']+)'\)", l)])
def lonely_boxes(x, tmax):
    pts = sorted(set([F(6 * k + j, 6) / d for d in x for k in range(int(tmax * d) + 1) for j in (1, 5)]))
    out = {}
    for a in pts:
        if a <= tmax and all(F(1, 6) <= (d * a) % 1 <= F(5, 6) for d in x):
            k = tuple((d * a).numerator // (d * a).denominator for d in x)
            U = min(F(6 * kk + 5, 6) / d for kk, d in zip(k, x)); out[k] = U - a
    return out
cnt = Counter(); widths = []
for c in cells:
    x = [F(1)] + [(a + b) / 2 for a, b in c]
    bx = lonely_boxes(x, F(3)); 
    for k in bx: cnt[k] += 1
    widths.append(max(bx.values()) if bx else None)
print(f"failing cells: {len(cells)} (only the first 25 are listed in the .out)")
print("boxes containing the centres:", cnt.most_common(10))
print("largest lonely width at the centres (min over cells):", min(w for w in widths if w is not None) if widths else None)
