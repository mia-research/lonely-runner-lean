import math
from fractions import Fraction as F
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
def clear_iv(x, T):
    out = []; n = 0
    while True:
        lo = F(8 * n + 1, 8) / x; hi = F(8 * n + 7, 8) / x
        if lo > T: break
        out.append((lo, min(hi, T))); n += 1
    return out
def meet(A, B):
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def widest_window(S):
    g = 0
    for d in S: g = math.gcd(g, d)
    T = F(2, g)
    J = clear_iv(F(S[0]), T)
    for s in S[1:]: J = meet(J, clear_iv(F(s), T))
    return max(J, key=lambda iv: iv[1] - iv[0])
def casc(S):
    t = F(1, 8 * min(S))
    while True:
        way = [d for d in S if dist(d * t) < E]
        if not way: return t
        t = max((F(round(d * t)) + E) / d for d in way)
