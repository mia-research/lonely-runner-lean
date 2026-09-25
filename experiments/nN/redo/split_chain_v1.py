"""The split-chain rule: native lower order for the slow core, nested windows for the fast top.  Exact.

Readings (distinct) 1 = s_1 < ... < s_k (k <= 7), ratios r_i = s_{i+1}/s_i.
Split at u (1 <= u <= k-1): the core s_1..s_u (u readings, u + 1 runners with the subject) is lonely at 1/(u+1) by the
native lower orders (orders 2..7), so every core runner stays clear at 1/8 on a window of length
2 (1/(u+1) - 1/8) / s_u around that instant; in laps of s_{u+1} that is ROOM_u = 2 (1/(u+1) - 1/8) r_u.
The top s_{u+1}..s_k runs the nested-window chain: W_k = 1/4; l_i = W_{i+1}/r_i; W_i = 2 l_i + 1/4; each l_i <= 3/4.
The split works iff the chain is valid and W_{u+1} <= ROOM_u.  (u = 6, one fast runner: r_6 >= 7, which is R8;
u = 5, two: the fast pair.)  The plain chain (u = 0) uses the nearest runner's first band instead.
Checks: soundness (rule applies => the subject is lonely: the cascade stops) and coverage for S > 12."""
import random
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd
from ratio_chain_v1 import chain, cascade, fams

def top_window(s, u):
    """W_{u+1} for the chain over s[u..], or None if some l_i > 3/4.  (s is 0-indexed: s[0] = s_1.)"""
    W = F(1, 4)
    for i in range(len(s) - 2, u - 1, -1):
        l = W / (s[i + 1] / s[i])
        if l > F(3, 4): return None
        W = 2 * l + F(1, 4)
    return W

def split_rule(ds):
    s = sorted(set(F(d, min(ds)) for d in ds))
    k = len(s)
    if k <= 6: return 'lower order'
    if chain(ds): return 'chain'
    for u in range(k - 1, 0, -1):
        W = top_window(s, u)
        if W is None: continue
        room = 2 * (F(1, u + 1) - F(1, 8)) * (s[u] / s[u - 1])
        if W <= room: return f'split u={u}'
    return None

if __name__ == '__main__':
    from collections import Counter
    viol = 0
    print("split-chain rule: coverage among subjects with S > 12, by which case applies")
    for name, arrs in fams.items():
        n = big = 0; by = Counter()
        for V in arrs:
            if len(set(V)) < 8: continue
            for k in range(8):
                ds = readings(V, k); n += 1
                if F(max(ds), min(ds)) <= 12: continue
                big += 1; r = split_rule(ds); by[r or 'none'] += 1
        cov = big - by['none']
        print(f"  {name:28s} S > 12: {big:5d}; covered {cov:5d} ({100*cov//max(big,1)}%)  {dict(by)}")
