# Exact sup of the shifted-gap of a pair (a=1, b=r): the longest stretch of time with no instant at which both are 1/8-clear, over [0, T].  Interval arithmetic on exact Fractions.
import sys
from fractions import Fraction as F
def clear_intervals(x, T):
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
def max_gap(r, T):
    J = meet(clear_intervals(F(1), T), clear_intervals(r, T))
    g = J[0][0] if J else T  # gap from time 0
    for i in range(1, len(J)): g = max(g, J[i][0] - J[i - 1][1])
    return g
D = int(sys.argv[1]); T = F(int(sys.argv[2]))
worst = (F(0), None)
for p in range(D, 6 * D + 1):
    r = F(p, D)
    g = max_gap(r, T)
    if g > worst[0]: worst = (g, r)
print('D', D, 'T', T, 'sup gap (in units of 1/a)', worst[0], '=', float(worst[0]), 'at r =', worst[1], '; bound used in pair_window: 3/4')
