"""The first-lap instants on the hard sets: blockers, overlap, and a falsified prediction.

Hard sets: the 28 sets of the v1 residual of [1,40] that no first-lap rule with q <= 8 certifies.
Reports: blockers per first-lap instant i/q + 1/(8e) and their depth; covering efficiency against
independence for hard, near-hard and ordinary sets (total load sum_d p_d is about 1.5 for all; the
hard sets differ in overlap); and a FALSIFIED prediction: with the flank free (any multiple of q),
first-lap instants certify 21 of 28 where random openings of the same flanks certify 28, and the
working flanks are small (4 to 9), not large.  Caveat: 'hard' is selected by the family failing, so
their doing worse than random there is largely selection; over the whole residual the rule fails on
28 sets where independent instants would fail on several hundred.
"""
import itertools, random
from math import prod
from fractions import Fraction as Fr
from math import gcd
from collections import Counter, defaultdict
_rs = __file__.replace('anti_alignment_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
def signed(x): x = x % 1; return x if x <= Fr(1, 2) else x - 1
nblk = Counter(); depth = Counter(); topshare = []; tops = Counter()
for S in hard:
    inst = []
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            for i in range(q):
                if gcd(i, q) != 1: continue
                t = Fr(i, q) + Fr(1, 8 * e)
                bl = [(d, signed(d * t)) for d in S if abs(signed(d * t)) < Fr(1, 8)]
                inst.append((q, e, i, bl))
    per = Counter(d for *_x, bl in inst for d, _ in bl)
    for *_x, bl in inst:
        nblk[len(bl)] += 1
        if len(bl) == 1: depth[round(float(abs(bl[0][1])) * 64)] += 1   # in 64ths; 8 = the edge
    top, cnt = per.most_common(1)[0]
    topshare.append(cnt / len(inst)); tops[(sorted(S).index(top) + 1)] += 1
print(f"28 hard sets: first-lap instants blocked by k disparities: {sorted(nblk.items())}")
print(f"  single-blocker depth |reading| in 64ths (8 = edge of the band): {sorted(depth.items())}")
print(f"  share of instants blocked by the busiest disparity: min {min(topshare):.2f} median {sorted(topshare)[14]:.2f} max {max(topshare):.2f};  its rank in the set: {sorted(tops.items())}")

def signed(x): x = x % 1; return x if x <= Fr(1, 2) else x - 1
def profile(S):
    inst = []
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            for i in range(q):
                if gcd(i, q) != 1: continue
                t = Fr(i, q) + Fr(1, 8 * e)
                inst.append(frozenset(d for d in S if abs(signed(d * t)) < Fr(1, 8)))
    n = len(inst)
    p = {d: sum(d in b for b in inst) / n for d in S}
    expected_free = n * prod(1 - p[d] for d in S)
    free = sum(1 for b in inst if not b)
    overlap = sum(len(b) for b in inst) / max(1, sum(1 for b in inst if b))   # mean blockers per blocked instant
    return n, free, expected_free, overlap, sum(p.values())
random.seed(12)
easy = random.sample([S for S in R40 if S not in set(f25)], 400)
for label, sets in (("28 hard", hard), ("1,586 failing q = 2..5", f25), ("400 ordinary residual", easy)):
    P = [profile(S) for S in sets]
    n = sum(x[0] for x in P) / len(P); fr = sum(x[1] for x in P) / len(P); ex = sum(x[2] for x in P) / len(P)
    ov = sum(x[3] for x in P) / len(P); load = sum(x[4] for x in P) / len(P)
    print(f"{label}: instants {n:.1f}; free observed {fr:.2f} vs independent {ex:.2f}; blockers per blocked instant {ov:.2f}; total blocking load sum_d p_d {load:.2f}")

def lonely_t(S, t): return all(Fr(1, 8) <= (d * t) % 1 <= Fr(7, 8) for d in S)
def free_family(S):
    """first-lap instants i/q + 1/(8e): q <= 8, e ANY multiple of q up to 8*max(S) (not required in S), i a unit"""
    out = []
    for q in range(2, 9):
        for e in range(q, 8 * max(S) + 1, q):
            for i in range(q):
                if gcd(i, q) == 1: out.append((q, e, i, Fr(i, q) + Fr(1, 8 * e)))
    return out
def links_diff(S, q):
    """|d' - c d| for residue-linked pairs mod q (c = +-1)"""
    return [abs(d2 - c * d) for d, d2 in itertools.combinations(S, 2) for c in (1, -1) if (d2 - c * d) % q == 0 and d % q and d2 % q]
random.seed(13)
res = Counter(); ratio = []
for S in hard:
    F = free_family(S)
    good = [(q, e, i) for q, e, i, t in F if lonely_t(S, t)]
    res['certified'] += bool(good)
    # null: same number of random openings of the same flanks
    res['null'] += any(lonely_t(S, Fr(8 * random.randrange(e) + 1, 8 * e)) for q, e, i, t in F)
    if good:
        q, e, i = min(good, key=lambda g: g[1])          # smallest working flank
        L = links_diff(S, q)
        ratio.append((e, q, min(L) if L else None, max(S), e in S))
print(f"28 hard sets, free flank (e any multiple of q <= 8, e <= 8 max), first lap: certified {res['certified']}/28; same number of random openings of those flanks: {res['null']}/28")
print("  smallest working flank e, its q, the smallest linked |d' -+ d| at that q, max(S), e in S?:")
for r in ratio: print("   ", r)
