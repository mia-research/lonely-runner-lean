"""How far past the first live lattice L_0 does the ladder go?

Ladder (PROOF_REQUIREMENTS_v2 section 7, v2 numerators): the least D with some a = 8j+1, j < D,
clearing every d (band D <= d*a mod 8D <= 7D).  Dead(D): 8D divides some d.  L_0 = least live D.
Statistic per set: D* - L_0, and k = the number of live lattices in [L_0, D*) (k = 0: L_0 clears).
Objects: rule-miss sets (hard_sets_41_60.json); random primitive 7-sets from [1,10^3] and [1,10^6];
ADVERSARIAL sets: one or two elements replaced by u * 8 * lcm(1..c), c = 4..16 -- every D <= c is
then dead, so L_0 > c; the question is whether D* stays near L_0 when the bottom is eaten.
"""
import json, random
from math import gcd, lcm
from functools import reduce
from collections import Counter

def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)
def dead(S, D): return any(d % (8 * D) == 0 for d in S)
def ladder(S):
    D = 1; live_before = 0; L0 = None
    while True:
        if not dead(S, D):
            if L0 is None: L0 = D
            for j in range(D):
                if clears(S, D, 8 * j + 1): return L0, D, live_before, 8 * j + 1
            live_before += 1
        D += 1

def report(label, sets):
    ks = Counter(); gaps = Counter(); worst = None
    for S in sets:
        L0, D, k, a = ladder(S); ks[k] += 1; gaps[D - L0] += 1
        if worst is None or k > worst[0]: worst = (k, S, L0, D, a)
    print(f"{label} ({len(sets)} sets):")
    print(f"  live steps past L_0, k: {sorted(ks.items())}")
    print(f"  D* - L_0: {sorted(gaps.items())}")
    print(f"  worst: k={worst[0]} at {worst[1]}, L_0={worst[2]}, D*={worst[3]}, a={worst[4]}")

rnd = random.Random(26)
def prim(lo, hi, n):
    out = set()
    while len(out) < n:
        S = tuple(sorted(rnd.sample(range(lo, hi + 1), 7)))
        if reduce(gcd, S) == 1: out.add(S)
    return sorted(out)
report("rule-miss sets, largest 41..60", [tuple(S) for S in json.load(open('hard_sets_41_60.json'))])
report("random primitive, [1, 10^3]", prim(1, 10**3, 3000))
report("random primitive, [1, 10^6]", prim(1, 10**6, 3000))
for c in (4, 6, 8, 10, 12, 14, 16):
    L = 8 * lcm(*range(1, c + 1)); adv = set()
    while len(adv) < 1000:
        base = rnd.sample(range(1, 10**4), 7)
        m = rnd.choice((1, 2))
        for idx in range(m): base[idx] = L * rnd.randrange(1, 50)
        S = tuple(sorted(set(base)))
        if len(S) == 7 and reduce(gcd, S) == 1: adv.add(S)
    report(f"adversarial, 8*lcm(1..{c}) = {L} divides one or two elements", sorted(adv))
