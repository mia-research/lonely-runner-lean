"""How lonely are the hard sets?  The gap delta(S) = max_t min_d ||d t||.

cluster_slack_v1: all 1,436 hard sets (no q <= 8 certifies) are lonely at 1/6, not just 1/8.
Exact gap: the max-min of the piecewise-linear ||d t|| is attained where two of them tie (or at a
peak 1/2 of one), so at t = m/(d_i + d_j) or m/(d_j - d_i); all such t in [0, 1) are checked.
Reported: the distribution of delta over the hard sets, over the whole [1,40] residual, and the
sets of least gap in each (the extremal ones).
"""
import itertools, json, os, time
from fractions import Fraction as F
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def nd(x): x = x % 1; return min(x, 1 - x)
def gap(S):
    """Integer arithmetic: at t = m/Q the value is min(r, Q - r)/Q, r = d*m mod Q; compare by cross-multiplying."""
    bn, bq = 0, 1
    dens = set()
    for d, e in itertools.combinations(S, 2):
        dens.add(d + e); dens.add(e - d)
    for Q in dens:
        for m in range(Q):
            v = Q
            for d in S:
                r = d * m % Q; r = min(r, Q - r)
                if r < v: v = r
                if v * bq <= bn * Q: break
            if v * bq > bn * Q: bn, bq = v, Q
    return F(bn, bq)
def bucket(g):
    for lab, th in (("< 1/7", F(1, 7)), ("[1/7, 1/6)", F(1, 6)), ("[1/6, 1/5)", F(1, 5)), ("[1/5, 1/4)", F(1, 4))):
        if g < th: return lab
    return ">= 1/4"
t0 = time.time()
gh = {S: gap(S) for S in H}
print("hard sets, largest 41..60:", sorted(Counter(bucket(g) for g in gh.values()).items()),
      "; least gap", min(gh.values()), [S for S, g in gh.items() if g == min(gh.values())][:4], f"({time.time()-t0:.0f}s)")
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
hardR = {S for S in R if not any(rule(S, q, free_exact) for q in range(2, 9))}
gr = {S: gap(S) for S in R}
print("[1,40] residual:", sorted(Counter(bucket(g) for g in gr.values()).items()))
print("   least gaps:", sorted(set(gr.values()))[:5], "sets at the least:", [S for S, g in gr.items() if g == min(gr.values())][:6])
print("   gap of the 28 [1,40] hard sets:", sorted(Counter(bucket(gr[S]) for S in hardR).items()), "least", min(gr[S] for S in hardR))
print("   residual sets with gap < 1/6:", sum(g < F(1, 6) for g in gr.values()), "of which hard:", sum(gr[S] < F(1, 6) for S in hardR))
print(f"total {time.time()-t0:.0f}s")
