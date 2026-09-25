"""The ratio-chain rule (nested windows, the pair_window argument iterated).  Exact.

Readings (distinct) 1 = s_1 < s_2 < ... < s_k, ratios r_i = s_{i+1}/s_i.  A runner is blocked on (j - 1/8, j + 1/8) of
its own laps, so a window of 2l + 1/4 of its laps holds a clear stretch of length l (l <= 3/4).  Top-down:
   W_k = 1/4 (the fastest needs one clear point);  l_i = W_{i+1} / r_i (in laps of s_i);  W_i = 2 l_i + 1/4;
the rule APPLIES iff every l_i <= 3/4 (i = 1..k-1).  Then the nearest runner's first clear band [1/8, 7/8] holds the
whole nest, so the subject is lonely at some R in [1, 7] (band 0).
Checks: (1) wherever the rule applies, the cascade's event is in band 0 (u* <= 7/8) -- a falsifiable consequence;
(2) coverage among subjects with S > 12, by family."""
import random
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd

def chain(ds):
    s = sorted(set(F(d, min(ds)) for d in ds))
    W = F(1, 4)
    for i in range(len(s) - 2, -1, -1):
        l = W / (s[i + 1] / s[i])
        if l > F(3, 4): return False
        W = 2 * l + F(1, 4)
    return True

def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)

rnd = random.Random(21)
def fam_loguniform(n, top):
    # seven readings with log-uniform ratios up to S = top
    out = []
    while len(out) < n:
        base = rnd.randint(1, 50)
        V = sorted(set([base] + [base + int(round(rnd.random() ** 3 * top * base)) + rnd.randint(1, 9) for _ in range(7)]))
        if len(V) == 8: out.append(V)
    return out
fams = {'uniform [1,1000]': [rnd.sample(range(1, 1001), 8) for _ in range(300)],
        'uniform [1,100000]': [rnd.sample(range(1, 100001), 8) for _ in range(300)],
        'skewed (many scales)': fam_loguniform(300, 10**5),
        'geometric-ish ratio 1.5..3': [sorted(set(int(1000 * F(rnd.randint(150, 300), 100) ** k) + rnd.randint(0, 5) for k in range(8))) for _ in range(300)]}
viol = 0
print("ratio-chain rule: coverage among subjects with S > 12, and soundness check (rule applies => event in band 0)")
for name, arrs in fams.items():
    n = big = app = 0
    for V in arrs:
        if len(set(V)) < 8: continue
        for k in range(8):
            ds = readings(V, k); n += 1
            S = F(max(ds), min(ds))
            a = chain(ds)
            if a:
                u = min(ds) * cascade(ds)
                if u > F(7, 8): viol += 1; print("  VIOLATION", V, k, u)
            if S > 12:
                big += 1; app += a
    print(f"  {name:28s} subjects {n:5d}; with S > 12: {big:5d}; rule applies: {app:5d}")
print(f"soundness violations (rule applies but event not in band 0): {viol}")
