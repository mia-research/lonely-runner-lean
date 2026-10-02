"""E264 (2026-10-02): independent check of the 6 hand-off counterexamples from restricted_b_v1.out Part 1 (seeds 206-208,
mode A).  Direct circDist (Fractions) at every opening u = 8k+1 of c's band run at the fastest flank e: who is in the
way (circDist(x t) < 1/8 with t = u/(8e)); c's own state; the hand-off's segments; the exact cascade landing; classify()."""
import sys, re, os
from fractions import Fraction as F
from math import floor
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
from quantity_tests_v1 import cd, E8
from hole_residual_v1 import classify
S6 = []
for line in open('restricted_b_v1.out'):
    m = re.match(r'\s+seed (\d+) mode A: \(([\d, ]+)\)', line)
    if m: S6.append((int(m.group(1)), tuple(int(x) for x in m.group(2).split(','))))
def cascade(T):
    t = F(1, 8 * min(T))
    while True:
        way = [d for d in T if cd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
out = open('ce6_verify_v1.out', 'w'); out.write(__doc__ + "\n")
def w(s): out.write(s + "\n"); out.flush()
for seed, S in S6:
    c = S[0]; cl = S[1:]; e = cl[-1]
    k0 = -((-(e - c)) // (8 * c)); k1 = (7 * e - c) // (8 * c)
    segs = []; cway = 0; free = 0
    for k in range(k0, k1 + 1):
        t = F(8 * k + 1, 8 * e)
        if cd(c * t) < E8: cway += 1
        ins = tuple(cl.index(x) + 1 for x in cl[:-1] if cd(x * t) < E8)
        if not ins: free += 1
        segs.append(ins)
    # occupant sets per opening -> maximal runs with a common walker
    runs = []; cur = None
    for ins in segs:
        if cur is None: cur = set(ins)
        elif cur & set(ins): cur &= set(ins)
        else: runs.append(sorted(cur)); cur = set(ins)
    runs.append(sorted(cur))
    t = cascade(S); lone = all(cd(d * t) >= E8 for d in S)
    rank = next(i for i, x in enumerate(S) if (8 * x * t) % 8 == 1)
    w("seed %d: openings in c's run %d; c in the way at %d; openings with the fastest flank free: %d; greedy segments %d (occupants %s...); cascade R=8*c*t=%.4f, lands at reading index %d (0 = c), lonely %s; classify: %s" % (
        seed, len(segs), cway, free, len(runs), runs[:6], float(8 * c * t), rank, lone, classify(S)[0]))
out.close(); print(open('ce6_verify_v1.out').read()[len(__doc__):])
