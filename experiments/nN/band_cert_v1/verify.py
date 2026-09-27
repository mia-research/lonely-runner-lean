"""EXACT verifier of the nested-partition certificate (fractions.Fraction only).

Claim verified: for every s = (1, s1, ..., s6) with 1 <= s1 <= ... <= s6 and 7 <= s6 <= 9,
some R in [1,7] u [9,Rhi] is clear.

Checks performed, all in exact rational arithmetic:
 (P) partition: top cells tile [7,9]; every sub-node at level L tiles [1, b_parent] with
     consecutive closed cells (first a = 1, last b = b_parent, a_{i+1} = b_i, a_i < b_i).
 (T) the robust R-set S is carried down exactly: S_L = S_{L+1} ∩ T[a,b],
     T[a,b] = U_k [(8k+1)/a, (8k+7)/b]   (Lemma 1).
 (B) at every level-2 cell, with S = S_2: the bad set
     Bad = ∩_{[p,q] in S} U_{m>=1} ((8m-1)/p, (8m+1)/q)   (Lemma 2)
     does not meet [1, b_2].
"""
import sys, pickle, time
from fractions import Fraction as F
from multiprocessing import Pool

ONE = F(1)

def T(a, b, Rlo, Rhi):
    out = []
    k = max(0, (a * Rlo - 7) // 8)
    while True:
        lo = (8 * k + 1) / a
        if lo > Rhi:
            break
        hi = (8 * k + 7) / b
        lo2 = lo if lo > Rlo else Rlo
        hi2 = hi if hi < Rhi else Rhi
        if lo2 <= hi2:
            out.append((lo2, hi2))
        k += 1
    return out

def inter_closed(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out

def inter_open(A, B):
    """A, B: sorted lists of OPEN intervals (lo<hi), each list pairwise disjoint."""
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo < hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out

def bad_meets(S, hi):
    """True iff Bad(S) meets [1,hi]."""
    bad = None
    for (p, q) in S:
        comp = []
        m = 1
        while True:
            lo = (8 * m - 1) / p
            if lo >= hi:
                break
            h = (8 * m + 1) / q
            if lo < h and h > ONE:
                comp.append((lo, h))
            m += 1
        # comp intervals are disjoint and sorted: (8m-1)/p increasing, and
        # (8m+1)/q <= (8m+1)/p < (8m+7)/p = (8(m+1)-1)/p.
        bad = comp if bad is None else inter_open(bad, comp)
        if not bad:
            return False
    # every remaining open interval has lo < hi (param) and h > 1 -> meets [1,hi]
    return len(bad) > 0

class Fail(Exception):
    pass

stats = {"cells": 0, "leaves": 0}

def check_node(node, S, L, lo, hi):
    if not node:
        raise Fail(("empty node", L, lo, hi))
    if F(node[0][0]) != lo or F(node[-1][1]) != hi:
        raise Fail(("partition ends", L, lo, hi))
    prev = lo
    for (a, b, sub) in node:
        a = F(a); b = F(b)
        if a != prev or not a < b:
            raise Fail(("partition gap", L, a, b, prev))
        prev = b
        stats["cells"] += 1
        S2 = inter_closed(S, T(a, b, S[0][0], S[-1][1])) if S else []
        if not S2:
            raise Fail(("empty S", L, a, b))
        if L == 2:
            if sub is not None:
                raise Fail(("level-2 cell has sub", a, b))
            if bad_meets(S2, b):
                raise Fail(("bad set meets", a, b, S2))
            stats["leaves"] += 1
        else:
            check_node(sub, S2, L - 1, ONE, b)

def job(args):
    a, b, tree, Rhi = args
    t = time.time()
    stats["cells"] = 0; stats["leaves"] = 0
    if tree is None:
        return (a, b, False, dict(stats), 0.0, "no certificate for this top cell")
    try:
        S0 = [(F(1), F(7)), (F(9), F(Rhi))]
        check_node(tree, S0, 6, F(a), F(b))
        return (a, b, True, dict(stats), time.time() - t, None)
    except Fail as e:
        return (a, b, False, dict(stats), time.time() - t, repr(e.args)[:400])

if __name__ == "__main__":
    cert = pickle.load(open(sys.argv[1], "rb"))
    Rhi = cert["Rhi"]; top = cert["top"]
    # top cells tile [7,9]
    ends = [(F(a), F(b)) for a, b, _ in top]
    assert ends[0][0] == 7 and ends[-1][1] == 9, "top range"
    assert all(ends[i][1] == ends[i + 1][0] for i in range(len(ends) - 1)), "top tiling"
    with Pool(10) as p:
        res = p.map(job, [(a, b, t, Rhi) for a, b, t in top], chunksize=1)
    ok = all(r[2] for r in res)
    cells = sum(r[3]["cells"] for r in res); leaves = sum(r[3]["leaves"] for r in res)
    print("Rhi =", F(Rhi), " top cells:", len(top), " cells checked:", cells, " level-2 leaves:", leaves)
    for r in res:
        if not r[2]:
            print("FAIL", r[0], r[1], r[5])
    print("ALL VERIFIED" if ok else "VERIFICATION FAILED")
