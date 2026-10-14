"""The 'hypothesis fails but BSM time = 1/(8m) + 1/(8D)' cases.  Integer readings s = d/m, exactly one slot-sharer S (8|S).
Move time t = 1/(8m) + 1/(8Dm)... in lap units u = 1/8 + 1/(8S).  A reading s moves by s/(8S) laps.
Failure reasons at p = 1:  (a) some reading larger than S;  (b) some non-sharer reading s = 7 (mod 8) (starts at 7/8).
For each offending runner: its phase before (s/8 mod 1) and after (s*u mod 1), in eighths."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor
from collections import Counter
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time
def fr(x): return x - floor(x)
def analyse(V, c, ex):
    V = [F(v) for v in V]
    for i in range(8):
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
        s = [d / m for d in ds]
        if any(x.denominator != 1 for x in s): continue
        s = [int(x) for x in s]; sh = [x for x in s if x % 8 == 0]
        if len(sh) != 1: continue
        S = sh[0]
        hyp = max(s) == S and all(1 <= x % 8 <= 6 for x in s if x != S)
        if hyp: continue
        u = F(1, 8) + F(1, 8 * S)
        t = first_time(V, i)
        if t != u / m: continue
        larger = [x for x in s if x > S]
        sevens = [x for x in s if x != S and x % 8 == 7]
        reason = ("sharer not the largest" if larger else "") + (" + " if larger and sevens else "") + ("a reading = 7 mod 8" if sevens else "")
        c[reason] += 1
        for x in larger:
            before, after = 8 * fr(F(x, 8)), 8 * fr(x * u)
            c[("larger reading", "moves more than 1 slot" if F(x, S) > 1 else "moves <= 1 slot",
               "lands in the same slot band as it started" if floor(before) == floor(after) else "lands in a different slot")] += 1
            if len(ex) < 6: ex.append((f"s={s} S={S}", f"larger reading {x}: {before} -> {after} eighths"))
        for x in sevens:
            c[("7 mod 8 reading", "after the move at", str(8 * fr(x * u)) if x < S else ">= S")] += 1
c = Counter(); ex = []
for x in range(8, 201):
    for V in [(1,2,3,4,5,6,7,x), (1,2,3,4,5,6,x-1,x), (1,2,3,4,5,x-2,x-1,x)]:
        if len(set(V)) == 8 and sorted(V) == list(V): analyse(V, c, ex)
rng = random.Random(22)
for _ in range(4000): analyse(sorted(rng.sample(range(1, 150), 8)), c, ex)
for k, v in sorted(c.items(), key=str): print(k, v)
print("examples:"); [print("  ", e) for e in ex]
