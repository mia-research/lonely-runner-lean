#!/usr/bin/env python3
"""Observation: the corner lemma. At a residue-isolation arrangement d (speeds with residues 1,2,3,4,5 mod 6, one each),
the lap boxes K1 = floor(d/6) (instant 1/6) and K5 = floor(5d/6) (instant 5/6). Check: (a) in each box, every pair
inequality is strict at d except the entry/exit pair (residue-1 runner e, residue-5 runner x), which is an equality in
both, and the two equalities are the same hyperplane d_x/d_e = c with opposite sides; (b) random perturbations of d
(relative size up to r) lie in K1 or K5; the largest r found safe (slack of the strict pairs). Also the tight set
(1,3,4,5,9) with its two lonely points."""
import random, itertools
from fractions import Fraction as F
def pairs(d, k):
    return {(i, j): (6 * k[j] + 5) * d[i] - (6 * k[i] + 1) * d[j] for i in range(5) for j in range(5) if i != j}
def check(d):
    K1 = tuple((6 * x) // 36 if False else (x // 6) for x in d)
    K1 = tuple(x // 6 for x in d); K5 = tuple((5 * x) // 6 for x in d)
    e = [i for i, x in enumerate(d) if x % 6 == 1]; xx = [i for i, x in enumerate(d) if x % 6 == 5]
    p1 = pairs(d, K1); p5 = pairs(d, K5)
    z1 = [ij for ij, v in p1.items() if v == 0]; z5 = [ij for ij, v in p5.items() if v == 0]
    neg = [ij for ij, v in list(p1.items()) + list(p5.items()) if v < 0]
    slack = min(min(v for v in p1.values() if v > 0), min(v for v in p5.values() if v > 0)) / max(d)
    return K1, K5, z1, z5, neg, slack, (e, xx)
import sys
DIV = int(sys.argv[1]) if len(sys.argv) > 1 else 40
random.seed(88)
res = []
for d in [(1,8,9,10,11),(1,14,15,16,17),(1,20,21,22,23),(1,2,3,4,5),(1,2,9,10,11),(7,8,9,10,11),(5,7,10,15,20)]:
    if sorted(x % 6 for x in d) != [1,2,3,4,5]: print(d, "not residue isolation"); continue
    K1, K5, z1, z5, neg, slack, ex = check(d)
    ok = 0; N = 2000; r = slack / DIV
    for _ in range(N):
        v = [F(x) * (1 + F(random.randint(-1000, 1000), 1000) * r) for x in d]
        b1 = all((6 * K1[j] + 5) * v[i] >= (6 * K1[i] + 1) * v[j] for i in range(5) for j in range(5) if i != j)
        b5 = all((6 * K5[j] + 5) * v[i] >= (6 * K5[i] + 1) * v[j] for i in range(5) for j in range(5) if i != j)
        ok += b1 or b5
    print(d, "K1", K1, "K5", K5, "tight pairs", z1, z5, "violated", neg, f"slack/max {float(slack):.3f}", f"perturbed (rel {float(r):.4f}) in K1 or K5: {ok}/{N}")
