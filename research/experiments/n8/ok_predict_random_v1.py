"""ok_predict_random_v1 -- predict the moment for randomly chosen non-integer speeds.

n = 8, individual isolation, threshold 1/8.  Each runner i takes a random
non-integer speed in (i-1, i+1) -- all eight displaced from the AP at once.

THE PREDICTION, per runner:     t* = 1 / (8 * d_min)

WHY IT IS DECIDABLE CHEAPLY.  For t < 1/(8*d_min) we have d_min*t < 1/8, so
||d_min*t|| = d_min*t < 1/8 and the runner cannot be lonely.  Nothing precedes
the bound.  So ONE BSM evaluation at t = 1/(8*d_min) -- seven comparisons --
settles whether the moment is there.  No window construction is needed.

When the evaluation fails, the moment is strictly later, and `first_isolation`
finds it by merging each constraint's boundary times in increasing order and
stopping at the first that passes.
"""
import heapq
from fractions import Fraction as F

N = 8
E = F(1, 8)

def lonely(V, i, t):
    for j in range(N):
        if j == i: continue
        x = (abs(V[i] - V[j]) * t) % 1
        if min(x, 1 - x) < E: return False
    return True

def predict(V, i):
    """The bound, and whether it is attained.  O(n), no windows built."""
    ds = [abs(V[i] - V[j]) for j in range(N) if j != i]
    t = E / min(ds)
    return t, lonely(V, i, t)

def first_isolation(V, i, cap=10**6):
    """Exact moment. Merges the per-constraint boundary times, stops at the first hit."""
    ds = [abs(V[i] - V[j]) for j in range(N) if j != i]
    h = [(E / d, d, 0, 1) for d in ds]
    heapq.heapify(h)
    tried = 0
    while h and tried < cap:
        t, d, k, s = heapq.heappop(h)
        heapq.heappush(h, ((F(8*(k+1)+1, 8) if s == 1 else F(8*(k+1)-1, 8)) / d, d, k+1, s))
        if s == 1: heapq.heappush(h, (F(8*k+7, 8) / d, d, k, -1))
        tried += 1
        if lonely(V, i, t): return t, tried
    return None, tried
