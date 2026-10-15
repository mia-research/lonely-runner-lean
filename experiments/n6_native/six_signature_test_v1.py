#!/usr/bin/env python3
"""Test of the lead: for primitive SixResidual sets whose largest element e = 6E is the unique
multiple of 6, is the largest-flank verdict a function of a finite signature of the other four
elements? Signatures tested, coarse to fine:
  s1: sorted (d mod 6)
  s2: sorted (d mod 6, d // E)
  s3: sorted (d mod 6, d // E, d mod E == 0)
A signature determines the verdict when no class contains both a working and a failing set.
Also reports the split of the residual by whether the largest element is the unique multiple of 6.
Exact integers."""
import sys, math, importlib.util
from itertools import combinations
from collections import defaultdict, Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def largest_ok(S):
    e = S[-1]
    return any(all(e <= (d * (6*k+1)) % (6*e) <= 5*e for d in S) for k in range(e))
split = Counter()
cls = {name: defaultdict(set) for name in ("s1", "s2", "s3")}
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]; M = sum(d % 6 == 0 for d in S)
    divlargest = (e % 6 == 0 and M == 1)
    ok = largest_ok(S)
    split[("largest=unique mult6" if divlargest else "other", ok)] += 1
    if not divlargest: continue
    E = e // 6; rest = S[:-1]
    sig = {"s1": tuple(sorted(d % 6 for d in rest)),
           "s2": tuple(sorted((d % 6, d // E) for d in rest)),
           "s3": tuple(sorted((d % 6, d // E, d % E == 0) for d in rest))}
    for name, s in sig.items(): cls[name][s].add(ok)
print(f"HI={HI}: split of residual (class, largest flank works) -> count: {dict(split)}")
for name, d in cls.items():
    mixed = sum(1 for v in d.values() if len(v) > 1)
    print(f"  {name}: classes={len(d)} mixed classes={mixed} classes with a failure={sum(1 for v in d.values() if False in v)}")
