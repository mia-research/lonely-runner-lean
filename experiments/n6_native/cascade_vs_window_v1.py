#!/usr/bin/env python3
"""Observation only. Where the cascade puts the isolation, against the lower-order window (E74).
(1) Family (1,2,3,4,L), L = lcm(1..Q0): cascade instant T, its final flank, the AP (1,2,3,4) window containing T,
    and the first-grid instant c/q* of E73.
(2) Primitive SixResidual <= 40: at the cascade instant T (the final flank b reads exactly 1/6), the other four runners'
    lonely window W at threshold 1/6 containing T; T's position in W (left end or inside); W's length times d_min;
    whether the four are also lonely at 1/5 somewhere in W (the order-five slack); whether b is the fastest runner."""
from fractions import Fraction as F
from collections import Counter
import math
def frac(x): return x - (x.numerator // x.denominator)
def cd(x): f = frac(x); return min(f, 1 - f)
def cascade(S):
    t = F(1, 6 * S[0]); fl = S[0]
    while True:
        b = [d for d in S if cd(d * t) < F(1, 6)]
        if not b: return t, fl
        o, d = max((F(6 * round(d * t) + 1, 6 * d), d) for d in b); t, fl = o, d
def window(R, t, q=F(1, 6)):
    """lonely interval of R at threshold q containing t (exact), via lap vector at t"""
    m = [(d * t).numerator // (d * t).denominator for d in R]
    L = max((k + q) / d for k, d in zip(m, R)); U = min((k + 1 - q) / d for k, d in zip(m, R))
    return L, U
def lonely_at(R, t, q): return all(q <= frac(d * t) <= 1 - q for d in R)
def slack_in(R, L, U, q=F(1, 5)):
    """some instant in [L,U] with R lonely at threshold q: check lap boxes meeting [L,U]"""
    lo = [math.floor(d * L) for d in R]; hi = [math.floor(d * U) for d in R]
    from itertools import product
    for m in product(*[range(a, b + 1) for a, b in zip(lo, hi)]):
        a = max([L] + [(k + q) / d for k, d in zip(m, R)]); b = min([U] + [(k + 1 - q) / d for k, d in zip(m, R)])
        if a <= b: return True
    return False
print("(1) family (1,2,3,4,L)")
for Q0 in (6, 12, 20, 28, 40):
    L = math.lcm(*range(1, Q0 + 1)); S = (1, 2, 3, 4, L); T, fl = cascade(S)
    W = window((1, 2, 3, 4), T)
    print(f"  Q0={Q0}: cascade T={T} (~{float(T):.5f}), final flank {fl if fl < 5 else 'L'}; AP window {W[0]}..{W[1]}; "
          f"T - window start = {float(T - W[0]):.2e}")
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
pos = Counter(); slack = Counter(); fastest = Counter(); lenb = Counter(); n = 0
for S in rows:
    T, b = cascade(S); R = tuple(d for d in S if d != b)
    Lw, Uw = window(R, T); n += 1
    pos["T at the window's left end" if T == Lw else "T inside the window"] += 1
    slack[slack_in(R, Lw, Uw)] += 1
    fastest[b == S[-1]] += 1
    lenb[round(float((Uw - Lw) * S[0]), 2)] += 1
print(f"(2) SixResidual sets {n}")
print("   cascade instant in the other four's 1/6-window:", dict(pos))
print("   the other four lonely at 1/5 somewhere in that window (order-five slack):", dict(slack))
print("   final flank is the fastest runner:", dict(fastest))
print("   window length x d_min, commonest:", lenb.most_common(8))
