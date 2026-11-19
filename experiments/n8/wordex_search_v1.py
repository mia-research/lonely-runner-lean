# wordex_search_v1 -- exact counterexample search for box-scoped word extraction.
# Box(n): g_i in [max(n_i-1/2,1), n_i+1/2].  Find g in box with:
#  (a) NO clear point: the open near-integer windows (g_i s/8 in (k-1/8,k+1/8)) COVER [9,15]
#  (b) NO realized word: no path in the zone DAG ((u,j) nodes, edges = overlap + j_p<j_q)
#      whose interval-union covers [9,15].
# Grid: each g_i on 1/16 steps within its face range.  Exact Fractions throughout.
from fractions import Fraction as F
from itertools import product
import sys

BOXES = {'b1344557': (1,3,4,4,5,5,7), 'b1345667': (1,3,4,5,6,6,7), 'b1445667': (1,4,4,5,6,6,7)}
STEP = F(1,4)

def face_range(n):
    lo = max(2*n-1, 2)
    hi = 2*n+1
    return F(lo,2), F(hi,2)

def grid_vals(n):
    lo, hi = face_range(n)
    vals = []
    x = lo
    while x <= hi:
        vals.append(x)
        x += STEP
    if vals[-1] != hi: vals.append(hi)
    return vals

def windows_cover(g, lo=F(9), hi=F(15)):
    """Do the 7 readings' open near-integer windows cover [lo,hi]? Exact: collect
    window intervals ((8k-1)/g, (8k+1)/g) meeting [lo,hi], sort, check coverage."""
    ivs = []
    for gi in g:
        k0 = int((lo*gi-1)/8) - 1
        k1 = int((hi*gi+1)/8) + 1
        for k in range(k0, k1+1):
            if k < 0: continue
            a, b = F(8*k-1,1)/gi, F(8*k+1,1)/gi
            a2, b2 = max(a, lo), min(b, hi)
            if a2 < b2: ivs.append((a2, b2))
    ivs.sort()
    if not ivs: return False
    if ivs[0][0] >= lo: return False     # point lo uncovered (open intervals)
    cur = ivs[0][1]
    for a, b in ivs[1:]:
        if a >= cur: return False        # gap or touch: uncovered point
        cur = max(cur, b)
    return cur > hi

def zone_intervals(g):
    """All (u,j) with I(u,j) = ((8j-1)/g_u,(8j+1)/g_u) meeting [9,15], j>=1."""
    nodes = []
    for u, gu in enumerate(g):
        if gu <= 0: continue
        j0 = max(1, int((9*gu-2)/8) - 1)
        j1 = int((15*gu+2)/8) + 1
        for j in range(j0, j1+1):
            a, b = F(8*j-1,1)/gu, F(8*j+1,1)/gu
            a2, b2 = max(a, F(9)), min(b, F(15))
            if a2 < b2:
                nodes.append((u, j, a2, b2, a, b))
    return nodes

def word_exists(g):
    """DFS for a path in the zone DAG whose union covers [9,15]."""
    nodes = zone_intervals(g)
    n = len(nodes)
    # adjacency: overlap inside [9,15] and j_p < j_q
    adj = {}
    for i in range(n):
        ui, ji, ai, bi, _, _ = nodes[i]
        for jj in range(n):
            uj, jj2, aj, bj, _, _ = nodes[jj]
            if ji < jj2 and max(ai,aj) < min(bi,bj):
                adj.setdefault(i, []).append(jj)
    # DFS from each start; state = (node, covered set as merged intervals list)
    from functools import lru_cache
    def merge(ivs):
        ivs = sorted(ivs); m = []
        for a,b in ivs:
            if m and a <= m[-1][1]: m[-1][1] = max(m[-1][1], b)
            else: m.append([a,b])
        return m
    def covers(m):
        cur = F(9)
        for a,b in m:
            if a > cur: return False
            cur = max(cur,b)
        return cur >= F(15)
    seen = set()
    def dfs(node, cov):
        key = (node, tuple(map(tuple,cov)))
        if key in seen: return None
        seen.add(key)
        ncov = merge(cov + [[nodes[node][2], nodes[node][3]]])
        if covers(ncov): return [node]
        for nxt in adj.get(node, []):
            # prune: skip if nxt fully inside covered
            r = dfs(nxt, ncov)
            if r is not None: return [node] + r
        return None
    for i in range(n):
        seen.clear()
        r = dfs(i, [])
        if r is not None:
            return [(nodes[k][0], nodes[k][1]) for k in r]
    return None

for name, box in BOXES.items():
    grids = [grid_vals(x) for x in box]
    total = 1
    for gr in grids: total *= len(gr)
    print(f"== {name} box={box} grid total={total}")
    noclear = 0; noword = 0; first = None
    count = 0
    for g in product(*grids):
        count += 1
        if count % 20000 == 0:
            print(f"  ...{count}/{total} noclear={noclear} noword={noword}", flush=True)
        if not windows_cover(g): continue
        noclear += 1
        if noclear > 400: continue   # cap the word searches per box
        w = word_exists(g)
        if w is None:
            noword += 1
            if first is None:
                first = g
                print("  CANDIDATE:", [str(x) for x in g], flush=True)
    print(f"  RESULT: no-clear-point instances={noclear}, of which no-word={noword}, first={[str(x) for x in first] if first else None}", flush=True)
