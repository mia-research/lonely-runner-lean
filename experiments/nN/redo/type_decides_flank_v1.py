"""Does the TYPE of an arrangement decide which flank carries a runner's isolation?

Type (author's picture: AP scale invariant, grid = AP with laps, slots monotone in speed order): for runner k of an
arrangement of 8 distinct positive whole-number speeds, read the arrangement against the AP of gap d_min from v_k
(CascadeRule.reading): runner j's slot is floor((v_j - v_k)/d_min), monotone in speed; its residue mod 8 is what a
position sees (whole laps invisible).  TYPE = (rank of k, the slot residues mod 8 of all eight in speed order).

Per runner, exact integer arithmetic (Theorem 6.14): flank e = |v_i - v_k| works at opening j < e iff every
difference d has e <= d(8j+1) mod 8e <= 7e.  Recorded: the set of flank RANKS (speed-order index of the flank runner)
that work at some opening, and the rank of the flank the cascade lands on (the runner at exactly 1/8 at t*).
Runners are deduplicated by their gcd-normalised signed differences (translates and dilates are the same object).
Question: within a type with >= 2 distinct members, is there one flank rank that works for all of them?"""
import sys, itertools, random
from fractions import Fraction as F
from math import gcd, floor
from functools import reduce
from collections import defaultdict, Counter

def nd(x): x = x % 1; return min(x, 1 - x)

def working_ranks(V, k):
    ds = [abs(v - V[k]) for j, v in enumerate(V) if j != k]
    out = set()
    for i in range(8):
        if i == k: continue
        e = abs(V[i] - V[k])
        for j in range(e):
            A = 8 * j + 1
            if all(e <= (d * A) % (8 * e) <= 7 * e for d in ds): out.add(i); break
    return out

def cascade_flank(V, k):
    ds = [abs(v - V[k]) for j, v in enumerate(V) if j != k]
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: break
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
    return {i for i in range(8) if i != k and (abs(V[i] - V[k]) * t) % 1 == F(1, 8)}

def type_of(V, k):
    m = min(abs(v - V[k]) for j, v in enumerate(V) if j != k)
    return (k, tuple(((v - V[k]) // m) % 8 for v in V))

def key_of(V, k):
    ds = [v - V[k] for v in V]; g = reduce(gcd, [abs(d) for d in ds if d])
    return tuple(d // g for d in ds)

def run(arrs, label):
    seen = set(); members = defaultdict(list)
    for V in arrs:
        for k in range(8):
            key = key_of(V, k)
            if key in seen: continue
            seen.add(key)
            members[type_of(V, k)].append((V, k, working_ranks(V, k), cascade_flank(V, k)))
    multi = {T: M for T, M in members.items() if len(M) >= 2}
    common = sum(1 for M in multi.values() if set.intersection(*[m[2] for m in M]))
    casc_const = sum(1 for M in multi.values() if len({frozenset(m[3]) for m in M}) == 1)
    none = sum(1 for M in members.values() for m in M if not m[2])
    print(f"\n== {label}: {len(seen)} distinct runners, {len(members)} types, {len(multi)} types with >= 2 members "
          f"(holding {sum(len(M) for M in multi.values())} runners)")
    print(f"   runners with no working flank: {none}")
    print(f"   types where ONE flank rank works for every member: {common} of {len(multi)}")
    print(f"   types where the cascade's flank rank is the same for every member: {casc_const} of {len(multi)}")
    sizes = Counter(len(M) for M in multi.values())
    print(f"   members per multi-member type: {dict(sorted(sizes.items())[:12])}")
    bad = [(T, M) for T, M in multi.items() if not set.intersection(*[m[2] for m in M])]
    for T, M in bad[:4]:
        print(f"   no common flank, type {T}:")
        for V, k, w, c in M[:4]: print(f"      {V} runner rank {k}: working flank ranks {sorted(w)}, cascade {sorted(c)}")
    return members

if __name__ == '__main__':
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    arrs = [(1,) + c for c in itertools.combinations(range(2, M + 1), 7)
            if reduce(gcd, [x - 1 for x in c]) == 1]
    run(arrs, f"every arrangement 1 = v1 < ... < v8 <= {M}, gcd of differences 1")
    rnd = random.Random(27); arrs = []
    while len(arrs) < 6000:
        V = tuple(sorted(rnd.sample(range(1, 400), 8)))
        if reduce(gcd, [x - V[0] for x in V[1:]]) == 1: arrs.append(V)
    run(arrs, "6,000 random arrangements in [1, 400]")
