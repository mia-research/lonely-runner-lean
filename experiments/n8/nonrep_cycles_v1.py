r"""
nonrep_cycles_v1  --  Point 2 of the brief: which state sequences are realisable, and
the cycle structure of the increment graph restricted to the BLOCKING set.

As x increases, t_rho = floor(e_rho x) jumps by +1 exactly when x crosses j/e_rho.
At a generic x only one coordinate jumps, so the state vector walks the Cayley graph
of (Z/8)^5 with generators the five unit vectors, all edges +1.

A stretch of x on which EVERY state is blocking is a directed path inside the induced
subgraph on the blocking set B.  Around any directed CYCLE each coordinate advances a
multiple of 8, and coordinate rho advances at rate e_rho, so a cycle traversed by a
real trajectory has frequency vector proportional to (e_1,e_3,e_5,e_7,e_rho0).

This computes, for each rho0:
   * the strongly connected components of the induced subgraph on B,
   * hence whether a blocked stretch can be arbitrarily long,
   * the longest directed path in B (if B is acyclic), which bounds the number of
     consecutive blocked cells.
Also: the structural decomposition of |B| (Point 1).
"""
import itertools, sys
from collections import Counter

FULL = frozenset(range(8))
BAD = {(rho, t): frozenset(r for r in range(8) if (rho*r+t) % 8 in (0, 7))
       for rho in range(1, 8) for t in range(8)}
ODD = frozenset({1,3,5,7}); EVEN = frozenset({0,2,4,6})

# ---- Point 1 decomposition ----
print("POINT 1 -- structural decomposition of the blocking count\n")
unit_states = list(itertools.product(range(8), repeat=4))
def ucov(st): 
    c = set()
    for rho, t in zip((1,3,5,7), st): c |= BAD[(rho,t)]
    return c
A = sum(1 for st in unit_states if ucov(st) >= ODD)      # units cover all odds
Bc = sum(1 for st in unit_states if ucov(st) >= EVEN)    # units cover all evens
C = sum(1 for st in unit_states if ucov(st) == FULL)
print(f"  four units alone, over 8^4 = 4096 states:")
print(f"     cover all 4 ODD  residues : A = {A}   (= 4! * 2^4 = {24*16})")
print(f"     cover all 4 EVEN residues : B = {Bc}")
print(f"     cover all of Z/8          : C = {C}")
print(f"     A = B by the reflection symmetry r -> -1-r, which swaps parities.\n")
print(f"  rho0 = 4:  bad(4,t) = evens for t in {{0,7}}, odds for t in {{3,4}}, EMPTY for")
print(f"             t in {{1,2,5,6}}.  So blocking count = 2A + 2B + 4C")
print(f"             = 2*{A} + 2*{Bc} + 4*{C} = {2*A+2*Bc+4*C}")
print(f"  rho0 in {{2,6}}: bad is one of the four cosets of {{0,4}}, each for exactly 2")
print(f"             values of t mod 8.  Blocking count = 2 * sum over the 4 cosets K of")
print(f"             #{{unit states whose cover contains Z/8 \\ K}}:")
for rho0 in (2, 6):
    cosets = {}
    for t in range(8): cosets.setdefault(frozenset(BAD[(rho0,t)]), []).append(t)
    tot = 0; parts = []
    for K, ts in sorted(cosets.items(), key=lambda kv: sorted(kv[0])):
        nK = sum(1 for st in unit_states if ucov(st) >= (FULL - K))
        parts.append(f"K={sorted(K)} (t in {ts}): {nK}")
        tot += len(ts)*nK
    print(f"     rho0={rho0}: " + "; ".join(parts) + f"   total = {tot}")

# ---- Point 2: cycles ----
print("\n\nPOINT 2 -- the increment graph on the blocking set\n")
def blocking(rho0):
    rhos = (1,3,5,7,rho0); out = set()
    for st in itertools.product(range(8), repeat=5):
        c = set()
        for rho, t in zip(rhos, st): c |= BAD[(rho,t)]
        if c == FULL: out.add(st)
    return out

def scc(nodes):
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [[] for _ in nodes]
    for v in nodes:
        for k in range(5):
            w = list(v); w[k] = (w[k]+1) % 8; w = tuple(w)
            if w in idx: adj[idx[v]].append(idx[w])
    n = len(nodes); index = [None]*n; low = [0]*n; on = [False]*n; st = []
    comps = []; counter = [0]
    for s in range(n):
        if index[s] is not None: continue
        work = [(s, 0)]
        while work:
            v, pi = work[-1]
            if pi == 0:
                index[v] = low[v] = counter[0]; counter[0] += 1
                st.append(v); on[v] = True
            recurse = False
            for i in range(pi, len(adj[v])):
                w = adj[v][i]
                if index[w] is None:
                    work[-1] = (v, i+1); work.append((w, 0)); recurse = True; break
                elif on[w]:
                    low[v] = min(low[v], index[w])
            if recurse: continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop(); on[w] = False; comp.append(nodes[w])
                    if w == v: break
                comps.append(comp)
            work.pop()
            if work:
                u = work[-1][0]; low[u] = min(low[u], low[v])
    return comps, adj, idx

for rho0 in (2, 4, 6):
    B = sorted(blocking(rho0))
    comps, adj, idx = scc(B)
    big = [c for c in comps if len(c) > 1]
    print(f"  rho0={rho0}: |B| = {len(B)};  SCCs: {len(comps)} total, "
          f"{len(big)} of size > 1  -> induced subgraph is "
          f"{'ACYCLIC (a DAG)' if not big else 'NOT acyclic'}")
    if not big:
        # longest directed path in the DAG
        order = []
        seen = [False]*len(B)
        def top():
            state = [(i, 0) for i in range(len(B))]
            res = []; mark = [0]*len(B)
            for s in range(len(B)):
                if mark[s]: continue
                stck = [(s, 0)]
                while stck:
                    v, pi = stck[-1]
                    if pi == 0:
                        if mark[v]: stck.pop(); continue
                        mark[v] = 1
                    adv = False
                    for i in range(pi, len(adj[v])):
                        w = adj[v][i]
                        if not mark[w]:
                            stck[-1] = (v, i+1); stck.append((w, 0)); adv = True; break
                    if adv: continue
                    mark[v] = 2; res.append(v); stck.pop()
            return res[::-1]
        order = top()
        dp = [0]*len(B)
        for v in reversed(order):
            for w in adj[v]:
                dp[v] = max(dp[v], dp[w]+1)
        L = max(dp)
        arg = B[dp.index(L)]
        print(f"      longest directed path has {L+1} vertices (start {arg});")
        print(f"      so a trajectory can sit inside the blocking set for at most {L+1}")
        print(f"      consecutive cells, and NO cycle of the increment graph lies in B.")
        print(f"      Consequence: no frequency vector is realisable, for ANY speeds.")
