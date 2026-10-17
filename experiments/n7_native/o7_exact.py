"""Exact integer band arithmetic for order seven (band [1/7, 6/7]). For a speed tuple S, time is scaled by
N = 7 lcm(S): the band edges (7m+1)/(7v) and (7m+6)/(7v) become the integers (7m+1) lcm/v and (7m+6) lcm/v, and one
period t in [0, 1) becomes [0, N). Every comparison is between integers; no floats."""
import math
from itertools import combinations
def lcm(S):
    out = 1
    for v in S: out = out * v // math.gcd(out, v)
    return out
def bands(v, M):
    q = M // v
    return [((7 * m + 1) * q, (7 * m + 6) * q) for m in range(v)]
def inter(A, B, strict=True):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if (hi > lo) if strict else (hi >= lo): out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def block(S, idx, M, strict=True):
    cur = bands(S[idx[0]], M)
    for k in idx[1:]: cur = inter(cur, bands(S[k], M), strict)
    return cur
def classify(S):
    """T4 / T5 / T6 / TIGHT / NOT LONELY, as o7_map_v1, exactly. Lengths in units 1/(7M), M = lcm(S):
    T4: U - L >= 2M/a + 2M/b;  T5: c (U - L) >= 2M."""
    n = len(S); M = lcm(S)
    full = block(S, range(n), M)
    if not full:
        return ("TIGHT" if block(S, range(n), M, strict=False) else "NOT LONELY"), None
    for idx in combinations(range(n), n - 2):
        rest = [k for k in range(n) if k not in idx]; a, b = S[rest[0]], S[rest[1]]
        need = 2 * M // a + 2 * M // b
        if any(U - L >= need for L, U in block(S, idx, M)): return "T4", tuple(k + 1 for k in rest)
    for idx in combinations(range(n), n - 1):
        r = [k for k in range(n) if k not in idx][0]
        if any(S[r] * (U - L) >= 2 * M for L, U in block(S, idx, M)): return "T5", (r + 1,)
    return "T6", None
def W_scaled(P):
    """(longest all-in-band length in units 1/(7M), M) for the tuple P, exact."""
    M = lcm(P); iv = block(P, range(len(P)), M)
    return max((U - L for L, U in iv), default=0), M
