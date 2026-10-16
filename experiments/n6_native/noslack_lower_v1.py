#!/usr/bin/env python3
"""Observation only. For the E75 sets without order-five slack: is the window supplied one order further down?
At the cascade instant T, for each 3-subset R of the five runners: R's 1/6-window containing T, and whether R is lonely
at 1/4 somewhere in it (order-four slack), the other two runners folding through. Also 2-subsets at 1/3."""
from fractions import Fraction as F
from collections import Counter
from itertools import combinations
exec(open("cascade_vs_window_v1.py").read().split('print("(1) family')[0])
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
res = Counter(); which = Counter(); n = 0
for S in rows:
    T, b = cascade(S); R4 = tuple(d for d in S if d != b); Lw, Uw = window(R4, T)
    if slack_in(R4, Lw, Uw): continue
    n += 1
    h3 = [R for R in combinations(S, 3) if slack_in(R, *window(R, T), q=F(1, 4))]
    h2 = [R for R in combinations(S, 2) if slack_in(R, *window(R, T), q=F(1, 3))]
    res[("some triple with 1/4 slack" if h3 else "no triple", "some pair with 1/3 slack" if h2 else "no pair")] += 1
    for R in h3: which[tuple(S.index(d) + 1 for d in R)] += 1
print(f"sets without order-five slack: {n}")
print(dict(res))
print("triples (speed ranks) with order-four slack around T, commonest:", which.most_common(10))
for S in rows:
    T, b = cascade(S); R4 = tuple(d for d in S if d != b); Lw, Uw = window(R4, T)
    if slack_in(R4, Lw, Uw): continue
    h3 = [R for R in combinations(S, 3) if slack_in(R, *window(R, T), q=F(1, 4))]
    h2 = [R for R in combinations(S, 2) if slack_in(R, *window(R, T), q=F(1, 3))]
    if not h3 and not h2: print("no lower-order slack at all:", S, "T =", T, "final flank", b, "readings", [str(frac(d * T)) for d in S])
