#!/usr/bin/env python3
"""As s5k1_obs_v1 (same types), with band-interval lists in floats intersected by a sweep (fast). EPS margin 1e-12.
§5 k = 1: v3 = v1 + v2, x3 = x1 + x2. Types of closing windows with t <= 3/v1:
  W123:s/a (block {1,2,3}, triangle same/apart, window_two on 4, 5), F5:s/a (block 1234), F4:s/a (block 1235),
  F3 (block 1245), F2 (block 1345), F1 (block 2345), BOX (all five)."""
import math, sys, random
from itertools import combinations
from collections import Counter
EPS = 1e-12
def bands(v, T):
    return [((m + 1 / 6) / v, (m + 5 / 6) / v, m) for m in range(int(T * v) + 1) if (m + 1 / 6) / v <= T]
def inter(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        a0, a1, la = A[i]; b0, b1, lb = B[j]
        lo, hi = max(a0, b0), min(a1, b1)
        if hi > lo + EPS: out.append((lo, hi, la + (lb,)))
        if a1 < b1: i += 1
        else: j += 1
    return out
def block(vs, T):
    cur = [(a, b, (m,)) for a, b, m in bands(vs[0], T)]
    for v in vs[1:]: cur = inter(cur, bands(v, T))
    return cur
def sharp(l, a, b):
    if l < 1 / (3 * a) + 1 / (3 * b) - EPS: return False
    m = 0
    while 3 * m * a < a + b:
        if (3 * m + 1) / (3 * b) > l + EPS: return False
        m += 1
    return True
def k1(S): return S[2] - S[1] == S[0] and S[2] > 3 * S[0]
def types(S):
    v1, v2, v3, v4, v5 = S; T = 3 / v1; out = set()
    b123 = block([v1, v2, v3], T)
    for L, U, ms in b123:
        tri = "s" if ms[2] == ms[0] + ms[1] else ("a" if ms[2] == ms[0] + ms[1] + 1 else "?")
        if sharp(U - L, v4, v5): out.add("W123:" + tri)
    for (x, y, nm) in ((v4, v5, "F5"), (v5, v4, "F4")):
        for L, U, ms in inter(b123, bands(x, T)):
            if y * (U - L) >= 1 / 3 - EPS:
                tri = "s" if ms[2] == ms[0] + ms[1] else "a"
                out.add(nm + ":" + tri)
    for blk, nm in (((0, 1, 3, 4), "F3"), ((0, 2, 3, 4), "F2"), ((1, 2, 3, 4), "F1")):
        r = [i for i in range(5) if i not in blk][0]
        if any(S[r] * (U - L) >= 1 / 3 - EPS for L, U, _ in block([S[i] for i in blk], T)): out.add(nm)
    if block(list(S), T): out.add("BOX")
    return out
def run(sets, label):
    av = Counter(); c = Counter(); ex = []; ex3 = []
    for S in sets:
        ts = types(S)
        for t in ts: av[t] += 1
        tri = any(t.startswith(("W123", "F5", "F4")) for t in ts)
        f3 = "F3" in ts
        key = "123-triangle and F3" if tri and f3 else ("123-triangle only" if tri else ("F3 only" if f3 else ("other" if ts else "NONE")))
        c[key] += 1
        if key == "other" and len(ex) < 12: ex.append((S, sorted(ts)))
        if key == "F3 only" and len(ex3) < 8: ex3.append(S)
    print(f"== {label}: {len(sets)} sets")
    print("   available:", dict(sorted(av.items(), key=lambda z: -z[1])))
    print("   closed by:", dict(c))
    print("   F3 only examples:", ex3)
    print("   neither (other types):", ex)
if __name__ == "__main__":
    H = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    run([S for S in combinations(range(1, H + 1), 5) if math.gcd(*S) == 1 and k1(S)], f"primitive §5 k=1 <= {H}")
    random.seed(51); big = []
    while len(big) < 2000:
        v1 = random.randint(1, 600); v2 = random.randint(2 * v1 + 1, 2000); v3 = v1 + v2
        v4 = random.randint(v3 + 1, 3 * v3); v5 = random.randint(v4 + 1, 4 * v3)
        S = (v1, v2, v3, v4, v5)
        if math.gcd(*S) == 1: big.append(S)
    run(big, "random §5 k=1")
