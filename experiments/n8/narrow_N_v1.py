"""E950: (a) class-N readings whose island has relative width below 10^-2 (E947: 5): their need (b - x_k)/b against the island's
extent on that side, exactly; (b) all class-N readings: is need <= extent on the escape side (the escape condition, E949 item 2)?"""
import pickle, glob
from fractions import Fraction as Fr
from math import floor
from collections import Counter
out = []
for f in sorted(glob.glob('island_vs_pass_v1_part*.pkl')): out += pickle.load(open(f, 'rb'))
E = Fr(1, 8); c = Counter()
for idx, k, kc, role, v0, L_, R_, a, b, P in out:
    if kc != 'N': continue
    w = (R_ - L_) / v0
    left = [(l, h, m) for l, h, m in P if h <= v0]; right = [(l, h, m) for l, h, m in P if l >= v0]
    nL = (v0 - max(left)[1]) / v0 if left else None; nR = (min(right)[0] - v0) / v0 if right else None
    eL = (v0 - L_) / v0; eR = (R_ - v0) / v0
    reachL = nL is not None and nL <= eL; reachR = nR is not None and nR <= eR
    c[('N: island reaches a pass interval on some side', reachL or reachR)] += 1
    if w < Fr(1, 100):
        print('E340', idx, 'reading', k, '| width %.3e | need L %s extent L %.3e | need R %s extent R %.3e (floats, steer only) | reaches: L %s R %s' % (
            float(w), None if nL is None else '%.3e' % float(nL), float(eL), None if nR is None else '%.3e' % float(nR), float(eR), reachL, reachR))
        c[('N narrower than 10^-2', 'reaches', reachL or reachR)] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
