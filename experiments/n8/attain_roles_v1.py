"""E949 start: the attaining readings of E945 against their role in the actual cascade (2026-11-25).  Exact Fractions.
For each of E340's 4,939 gate crossers: the opener o (the setter of the last move, so R* is o's exit), the closer(s)
(E945), and for each non-closer reading k its class (E945: L, P, X attain; N escapes).  Recorded: is the opener
attaining; class of the opener; is W_k = [R*, end] exactly for non-opener non-closer k (checked from windows of the six)."""
import pickle, glob, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('island_ends_v2.py').read().split("mode = sys.argv[1]")[0])
c = Counter()
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    o = rs.index(path[-1]) + 1
    c[('opener class', cls.get(o, 'C?') if o not in closers else 'closer')] += 1
    c[('opener attains', o in att)] += 1
    # landing window of the seven: [T, end]
    ws7 = windows(rs, E, T1); w7 = next((x, y) for x, y, z in ws7 if x <= T <= y)
    for k in range(2, 8):
        if k in closers: continue
        six = rs[:k - 1] + rs[k:]
        ws = windows(six, E, T1); wk = next((x, y) for x, y, z in ws if x <= T <= y)
        role = 'opener' if k == o else 'other'
        c[('W_k vs seven-window', role, 'start equal' if wk[0] == w7[0] else 'starts earlier', 'end equal' if wk[1] == w7[1] else 'end differs')] += 1
        c[('class by role', role, cls[k])] += 1
    c[('attaining set roles', tuple(sorted(('o' if k == o else 'x') + cls[k] for k in att)))] += 0
    c[('some non-opener attains', any(k != o for k in att))] += 1
for kk, v in sorted(c.items(), key=str):
    if v: print(v, '|', kk)
