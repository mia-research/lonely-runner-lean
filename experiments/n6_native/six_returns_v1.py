#!/usr/bin/env python3
"""Returns in the walk (observation), all 17,135 residual sets in [1,40].
An IMMEDIATE return: states (x, P) -> (y, Q) -> (x, P') with x in the way at y's opening. The framework's
return lemma (TerminationFour.return_lemma, n = 6) requires 4Q < 2P + 1. Checks it on every immediate
return, and records (P, Q, P'). A DELAYED return: the setter x reappears after two or more other moves;
records the number of intervening moves and the lap pattern. Exact Fractions."""
from fractions import Fraction as F
from collections import Counter
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s = l.split("\t")[0]; rows.append(eval(s))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); states = [(S[0], 0)]
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return states
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        t = best[0]; states.append((best[1], best[2]))
imm = Counter(); imm_bad = 0; delayed = Counter(); n_imm = n_del = 0; sets_with_return = 0
for S in rows:
    st = walk(S)[1:]   # moves only
    seen = {}; had = False
    for i, (x, P) in enumerate(st):
        if x in seen:
            had = True
            j = seen[x]; gap = i - j - 1
            if gap == 1:
                n_imm += 1
                Pp = st[j][1]; Q = st[j + 1][1]
                imm[(Pp, Q, P)] += 1
                imm_bad += not (4 * Q < 2 * Pp + 1)
            else:
                n_del += 1
                delayed[(gap, tuple(k for _, k in st[j:i + 1]))] += 1
        seen[x] = i
    sets_with_return += had
print(f"sets with a return: {sets_with_return}; immediate returns: {n_imm}; delayed returns: {n_del}")
print(f"  immediate returns violating 4Q < 2P + 1: {imm_bad}")
print("  immediate returns by (P, Q, P'):", imm.most_common(10))
print("  delayed returns by (moves in between, laps along the way):", delayed.most_common(10))
