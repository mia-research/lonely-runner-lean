"""Wrap versus tie split of the disagreement between slot descent (D) and rank fall (F).  Exact Fractions.

Population as grid_deviation_chain_rank_v1.py: 7-subsets of [1,N], gcd 1, landing opened by a reading clear at start.
For each consecutive pair of setters (a then b), reading rho, slot s = floor(rho) mod 8 with 0 read as 8, octave
o = floor(rho/8).  The pair DISAGREES when (rho_b < rho_a) differs from (s_b < s_a).  Each disagreeing pair gets one cause:
  tie       s_b == s_a
  wrap      s_b != s_a, octaves differ
  zero      s_b != s_a, same octave, one of the two slots is 0 (so the 0-read-as-8 convention flips the order)
  other     anything else (the hypothesis 'wrap and tie account for all' needs this to be 0; 'zero' is reported apart)
Chain level: D and F disagree  <=>  some pair disagrees (checked).  Counts only.
"""
import sys
from fractions import Fraction as F
from itertools import combinations
from math import gcd, floor
from collections import Counter
from functools import reduce

N = int(sys.argv[1]) if len(sys.argv) > 1 else 22


def blockers(R, rho):
    out = []
    for i, r in enumerate(rho):
        x = R * r
        z = floor(x / 8 + F(1, 2))
        if abs(x - 8 * z) < 1:
            out.append((i, z, (8 * z + 1) / r))
    return out


def run(rho):
    R, chain = F(1), []
    while True:
        b = blockers(R, rho)
        if not b:
            return chain
        i, z, nxt = max(b, key=lambda t: t[2])
        chain.append(i)
        R = nxt


pairs = Counter()
chains = Counter()
check_bad = 0
first_zero = []
n = 0
for S in combinations(range(1, N + 1), 7):
    if reduce(gcd, S) != 1:
        continue
    m = S[0]
    rho = [F(y, m) for y in S]
    q = [y // m for y in S]
    slot0 = [x % 8 for x in q]
    slot = [8 if s == 0 else s for s in slot0]
    octv = [x // 8 for x in q]
    epos = [y % m != 0 for y in S]
    start_blk = [slot0[i] == 0 or (slot0[i] == 7 and epos[i]) for i in range(7)]
    chain = run(rho)
    if not chain or start_blk[chain[-1]]:
        continue
    n += 1
    causes = set()
    D = all(slot[chain[k]] > slot[chain[k + 1]] for k in range(len(chain) - 1))
    Fall = all(chain[k + 1] < chain[k] for k in range(len(chain) - 1))   # index order = reading order
    for k in range(len(chain) - 1):
        a, b = chain[k], chain[k + 1]
        pairs["pairs"] += 1
        fall = b < a
        desc = slot[b] < slot[a]
        if fall == desc:
            continue
        if slot[b] == slot[a]:
            c = "tie"
        elif octv[a] != octv[b]:
            c = "wrap"
        elif slot0[a] == 0 or slot0[b] == 0:
            c = "zero"
        else:
            c = "other"
        pairs[c] += 1
        causes.add(c)
        if c == "zero" and len(first_zero) < 4:
            first_zero.append((S, chain, [slot[i] for i in chain]))
    if (D != Fall) != bool(causes):
        check_bad += 1
    if D != Fall:
        chains[tuple(sorted(causes))] += 1
    else:
        chains["agree"] += 1

print("N =", N, " chains:", n, " chains where 'D != F' disagrees with 'some pair disagrees':", check_bad)
print("pairs:", dict(pairs))
print("chain level (D != F):")
for k, v in sorted(chains.items(), key=lambda t: -t[1]):
    print("   ", k, v)
print("examples with a zero-convention pair (S; chain as reading indices 0..6; slots):")
for e in first_zero:
    print("  ", e)
