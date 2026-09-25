"""Every lonely cell contains a mirror meeting of its boundary flanks (the user's second canonical form).

A lonely cell [L, R]: L = (j_L + 1/8)/e_L (flank e_L leaves its zone), R = (k_R - 1/8)/e_R (flank e_R
enters one).  f(t) = (e_L + e_R) t - (j_L + k_R) has f(L) <= 0 <= f(R), so the cell contains
t_m = (j_L + k_R)/(e_L + e_R), where e_L and e_R read symmetrically (a mirror merge).
Here, per set: the FIRST lonely cell (L is the cascade's first isolation, Theorem 11), its boundary
pair, the ranks of e_L and e_R (0 = largest), Q = e_L + e_R and m = j_L + k_R; checked that t_m is
lonely; and how often the pair is the top pair (the D2 guess).  On the hard sets with largest
41..60 and on 3,000 random non-hard residual sets of [1,60].
"""
import json, os, random, math
from fractions import Fraction as F
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def nd(x): x = x % 1; return min(x, 1 - x)
def lonely(S, t): return all(nd(d * t) >= F(1, 8) for d in S)
def first_cell(S):
    t = F(1, 8) / min(S)
    while True:                                   # the cascade (Theorem 11)
        way = [d for d in S if nd(d * t) < F(1, 8)]
        if not way: break
        nxt = []
        for d in way:
            N = math.floor(d * t - F(1, 8)); o = (N + F(1, 8)) / d
            if o < t: o = (N + 1 + F(1, 8)) / d
            nxt.append(o)
        t = max(nxt)
    L = t; eL = [d for d in S if (d * L) % 1 == F(1, 8)]   # flanks leaving their zone at L
    eL = eL[0]
    jL = math.floor(eL * L)
    # R: the earliest entry (k - 1/8)/d > L over all d
    R = None; eR = kR = None
    for d in S:                                    # the earliest entry (k - 1/8)/d >= L (L = R: a one-point cell)
        k = math.ceil(d * L + F(1, 8))
        x = (k - F(1, 8)) / d
        if x < L: k += 1; x = (k - F(1, 8)) / d
        if R is None or x < R: R, eR, kR = x, d, k
    return L, R, eL, jL, eR, kR
def study(sets, label):
    ranks = Counter(); top = 0; ok = 0; same = 0
    for S in sets:
        L, R, eL, jL, eR, kR = first_cell(S)
        tm = F(jL + kR, eL + eR)
        ok += L <= tm <= R and lonely(S, tm)
        srt = sorted(S, reverse=True)
        ranks[(srt.index(eL), srt.index(eR))] += 1
        top += {eL, eR} == set(srt[:2]); same += eL == eR
    print(f"{label} ({len(sets)}): mirror centre in the first cell and lonely: {ok}; boundary pair is the top pair: {top}; e_L = e_R: {same}")
    print("   (rank of e_L, rank of e_R), 0 = largest, most common:", ranks.most_common(10))
study(H, "hard sets, largest 41..60")
random.seed(2); easy = []
while len(easy) < 3000:
    S = tuple(sorted(random.sample(range(1, 61), 7)))
    if eight_residual(S) and any(rule(S, q, free_exact) for q in range(2, 9)): easy.append(S)
study(easy, "non-hard residual sets of [1,60]")
