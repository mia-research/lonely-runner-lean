"""
rate_route_a_cycles_v2.py

Route A, honest model.  As b -> b+1 the floor vector T changes by a 0/1 vector,
NOT necessarily a single unit vector: coordinate rho advances exactly when
m_rho = L/e_rho divides b, and two coordinates advance together whenever
lcm(m_rho,m_sigma) | b.  So the increment graph must carry an edge
s -> s + chi_S for EVERY non-empty S subset of {1,3,5,7,rho0}, with both
endpoints in BAD (the intermediate states are never visited).

This script reports, for that full graph:
  * the strongly connected components,
  * which coordinates each cyclic SCC can advance,
  * hence the cone of cycle-frequency vectors.

Exact integer arithmetic only.
"""
import sys
from itertools import product

from rate_bad_states_v1 import build_bad, RHOS_UNIT

sys.setrecursionlimit(200000)

SUBSETS = [S for S in product((0, 1), repeat=5) if any(S)]


def build_graph_full(bad):
    adj = {s: [] for s in bad}
    for s in bad:
        for S in SUBSETS:
            t = tuple((s[i] + S[i]) % 8 for i in range(5))
            if t in bad:
                adj[s].append((t, S))
    return adj


def sccs(adj):
    index, low, onstk, stk, out = {}, {}, {}, [], []
    ctr = [0]
    for root in adj:
        if root in index:
            continue
        work = [(root, iter(adj[root]))]
        index[root] = low[root] = ctr[0]; ctr[0] += 1
        stk.append(root); onstk[root] = True
        while work:
            v, it = work[-1]
            adv = False
            for w, _ in it:
                if w not in index:
                    index[w] = low[w] = ctr[0]; ctr[0] += 1
                    stk.append(w); onstk[w] = True
                    work.append((w, iter(adj[w]))); adv = True; break
                elif onstk.get(w):
                    low[v] = min(low[v], index[w])
            if adv:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stk.pop(); onstk[w] = False; comp.append(w)
                    if w == v:
                        break
                out.append(comp)
    return out


def main():
    for rho0 in (2, 4, 6):
        bad = build_bad(rho0)
        adj = build_graph_full(bad)
        nedges = sum(len(v) for v in adj.values())
        comps = sccs(adj)
        cyc = []
        for c in comps:
            if len(c) > 1:
                cyc.append(c)
            else:
                s = c[0]
                if any(w == s for w, _ in adj[s]):   # self-loop (impossible: S non-empty)
                    cyc.append(c)
        cyc.sort(key=len, reverse=True)
        print(f"===== rho0={rho0}  |BAD|={len(bad)}  edges (all 31 subsets)={nedges} =====")
        print(f"  cyclic SCCs: {len(cyc)}; sizes: {sorted((len(c) for c in cyc), reverse=True)[:12]}")

        # for each cyclic SCC: which coordinates can advance on an INTERNAL edge
        for c in cyc[:20]:
            S = set(c)
            touched = [0] * 5
            for s in c:
                for w, lab in adj[s]:
                    if w in S:
                        for i in range(5):
                            touched[i] |= lab[i]
            rhos = RHOS_UNIT + (rho0,)
            names = [str(rhos[i]) for i in range(5) if touched[i]]
            print(f"    SCC size {len(c):3d}: internal edges advance coordinates "
                  f"{{{','.join(names)}}}   base {sorted(c)[0]}")
        # can any cyclic SCC advance all five?
        full = 0
        for c in cyc:
            S = set(c)
            touched = [0] * 5
            for s in c:
                for w, lab in adj[s]:
                    if w in S:
                        for i in range(5):
                            touched[i] |= lab[i]
            if all(touched):
                full += 1
        print(f"  cyclic SCCs able to advance ALL FIVE coordinates: {full}")
        print(f"  => every cycle has at least one coordinate with increment count 0"
              if full == 0 else
              f"  => Route A relaxation admits five-coordinate cycles")
        print()


if __name__ == "__main__":
    main()
