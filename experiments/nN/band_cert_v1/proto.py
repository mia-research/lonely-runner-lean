"""Float prototype of the nested cover search (search only; no decision is taken from it)."""
import sys, math, time
sys.setrecursionlimit(10000)
EPS = -1e-12

def T_interval(a, b, Rlo, Rhi):
    # robust good R-set for all x in [a,b]: union_k [(8k+1)/a, (8k+7)/b]
    out = []
    k = max(0, math.floor((a * Rlo - 7) / 8))
    while True:
        lo = (8 * k + 1) / a
        if lo > Rhi: break
        hi = (8 * k + 7) / b
        lo2, hi2 = max(lo, Rlo), min(hi, Rhi)
        if lo2 <= hi2 - EPS:
            out.append((lo2, hi2))
        k += 1
    return out

def inter(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi - EPS: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out

def TS(S, a, b):
    if not S: return []
    return inter(S, T_interval(a, b, S[0][0], S[-1][1]))

def last_ok(S, hi):
    # every x in [1,hi] has S ∩ T({x}) nonempty ; bad for comp [p,q]: union_m ((8m-1)/p,(8m+1)/q)
    bad = [(1.0, hi)]
    for (p, q) in S:
        comp = []
        m = max(1, math.floor((1 * p + 1) / 8))
        while True:
            lo = (8 * m - 1) / p; hi2 = (8 * m + 1) / q
            if lo > hi: break
            if lo < hi2: comp.append((lo, hi2))
            m += 1
        # intersect bad with comp (open intervals; treat as closed with margin)
        bad = inter_open(bad, comp)
        if not bad: return True
    return False

def inter_open(A, B):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo < hi + 1e-9: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out

nodes = 0
MINW = 1e-4

def cover(S, level, a, b):
    """cover coordinate `level` over [a,b]; subsequent coords range [1, b]."""
    global nodes
    nodes += 1
    S2 = TS(S, a, b)
    ok = False
    if S2:
        if level == 2:
            ok = last_ok(S2, b)
        else:
            ok = cover_range(S2, level - 1, 1.0, b)
    if ok: return True
    if b - a < MINW: return False
    m = (a + b) / 2
    return cover(S, level, a, m) and cover(S, level, m, b)

def cover_range(S, level, a, b):
    return cover(S, level, a, b)

if __name__ == "__main__":
    S0 = [(1.0, 7.0), (9.0, 15.0)]
    lo6, hi6 = float(sys.argv[1]), float(sys.argv[2])
    t = time.time()
    r = cover(S0, 6, lo6, hi6)
    print(r, nodes, time.time() - t)
