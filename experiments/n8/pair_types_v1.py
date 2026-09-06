#!/usr/bin/env python3
"""Which 2-subsets of a mod-163 class can a single speed cover?  (k=7, p=163.)

Inside class C_r = {r, r+163, r+326, r+489}, a speed v covers the target indexed
by t iff (a + t*v) mod 8 lies in the covering blocks {0,7}, where a depends on r.
So the coverable subsets S_v(r) are controlled by v mod 8 alone:

  v odd     -- S is an ADJACENT pair {t, t+1 mod 4}, or a singleton, or empty
  v = 4u    -- S is {0,2} or {1,3} (an OPPOSITE pair), or empty
  v = 2u    -- S is a singleton, always
  8 | v     -- S is {0,1,2,3} or empty

CONSEQUENCE.  {0,2} and {1,3} are complementary; so are {0,1}/{2,3} and
{1,2}/{0,3}.  An adjacent pair and an opposite pair are NEVER complementary.
So two speeds each contributing 2 targets can complete a class only if they are
both odd, or both = 4u -- never one of each.
"""
from collections import defaultdict
N, H, p = 1304, 652, 163

def covers(j, v):
    r = (j * v) % N
    return r < p or r > N - p

def v2(v):
    e = 0
    while v % 2 == 0:
        v //= 2; e += 1
    return e

seen = defaultdict(set)
for v in range(1, H + 1):
    if v % p == 0:
        continue
    e = min(v2(v), 3)
    for r in range(1, p + 1):
        S = frozenset(t for t in range(4) if covers(r + p * t, v))
        seen[e].add(S)

ADJ = {frozenset({0,1}), frozenset({1,2}), frozenset({2,3}), frozenset({0,3})}
OPP = {frozenset({0,2}), frozenset({1,3})}
name = {0: "v odd  ", 1: "v = 2u ", 2: "v = 4u ", 3: "8 | v  "}
for e in sorted(seen):
    sets = sorted(seen[e], key=lambda s: (len(s), sorted(s)))
    twos = {s for s in sets if len(s) == 2}
    tag = ("adjacent only" if twos and twos <= ADJ else
           "opposite only" if twos and twos <= OPP else
           "none of size 2" if not twos else "MIXED")
    print(f"{name[e]}  subsets seen: {[sorted(s) for s in sets]}   size-2 type: {tag}")

print("\nadjacent pair + opposite pair ever complementary:",
      any(a | o == {0,1,2,3} for a in ADJ for o in OPP))
