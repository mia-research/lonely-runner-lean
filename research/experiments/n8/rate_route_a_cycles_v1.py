"""
rate_route_a_cycles_v1.py

ROUTE A diagnostic: is the cycle-frequency relaxation strong enough to close
the problem on its own?

Graph: vertices = BAD(rho0); edge s -> s + u_rho for each rho (single-coordinate
increment), present iff both endpoints are in BAD.  Around any cycle every
coordinate returns to its value mod 8, so each coordinate's increment count is
divisible by 8.  Route A asks whether any cycle frequency vector is proportional
to an admissible speed vector (e_rho > 0, e_rho = rho mod 8).

If one is, Route A cannot close the problem: the relaxation admits a
counterexample that the actual dynamics does not.

Exact integer arithmetic only.
"""
import random
import sys
from math import gcd
from itertools import product, combinations_with_replacement

from rate_bad_states_v1 import build_bad, RHOS_UNIT

sys.setrecursionlimit(100000)


def build_graph(bad, rho0):
    adj = {s: [] for s in bad}
    for s in bad:
        for i in range(5):
            t = list(s)
            t[i] = (t[i] + 1) % 8
            t = tuple(t)
            if t in bad:
                adj[s].append((t, i))
    return adj


def sccs(adj):
    """Iterative Tarjan."""
    index = {}
    low = {}
    onstk = {}
    stk = []
    out = []
    counter = [0]
    for root in adj:
        if root in index:
            continue
        work = [(root, iter(adj[root]))]
        index[root] = low[root] = counter[0]; counter[0] += 1
        stk.append(root); onstk[root] = True
        while work:
            v, it = work[-1]
            advanced = False
            for w, _ in it:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stk.append(w); onstk[w] = True
                    work.append((w, iter(adj[w])))
                    advanced = True
                    break
                elif onstk.get(w):
                    low[v] = min(low[v], index[w])
            if advanced:
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


def cycle_vectors(adj, comp, rounds=4000, seed=1):
    """Randomised cycle extraction inside one SCC.  Returns set of type-count
    vectors (n_1,n_3,n_5,n_7,n_0) of simple cycles found."""
    rnd = random.Random(seed)
    S = set(comp)
    vecs = set()
    for _ in range(rounds):
        start = comp[rnd.randrange(len(comp))]
        path = [start]
        pos = {start: 0}
        types = []
        cur = start
        for _ in range(3000):
            opts = [(w, i) for w, i in adj[cur] if w in S]
            if not opts:
                break
            w, i = opts[rnd.randrange(len(opts))]
            types.append(i)
            if w in pos:
                j = pos[w]
                n = [0] * 5
                for tt in types[j:]:
                    n[tt] += 1
                vecs.add(tuple(n))
                break
            pos[w] = len(path)
            path.append(w)
            cur = w
    return vecs


def admissible_from_vector(n, rho0):
    """Given a cycle count vector n (order 1,3,5,7,rho0), decide whether some
    admissible speed vector is proportional to it.  Exact integer arithmetic.
    Returns e or None."""
    if any(x <= 0 for x in n):
        return None
    for x in n:
        if x % 8 != 0:
            return None            # must hold for a genuine cycle
    g = 0
    for x in n:
        g = gcd(g, x)
    u = tuple(x // g for x in n)   # primitive direction
    rhos = RHOS_UNIT + (rho0,)
    for lam in range(1, 8 * 200):
        e = tuple(lam * x for x in u)
        if all(ei % 8 == r % 8 for ei, r in zip(e, rhos)):
            if len(set(e)) == 5:
                return e
    return None


def main():
    for rho0 in (2, 4, 6):
        bad = build_bad(rho0)
        adj = build_graph(bad, rho0)
        nedges = sum(len(v) for v in adj.values())
        comps = [c for c in sccs(adj) if len(c) > 1]
        comps.sort(key=len, reverse=True)
        print(f"===== rho0={rho0}  |BAD|={len(bad)}  edges={nedges} =====")
        print(f"  non-singleton SCCs: {len(comps)}; sizes (top 8): "
              f"{[len(c) for c in comps[:8]]}")
        if not comps:
            print("  no cycles at all -- Route A would close it outright")
            continue

        allvecs = set()
        for c in comps[:6]:
            allvecs |= cycle_vectors(adj, c, rounds=3000, seed=hash((rho0, len(c))) % 10**6)
        print(f"  distinct simple-cycle count vectors sampled: {len(allvecs)}")
        div8 = [v for v in allvecs if all(x % 8 == 0 for x in v)]
        allpos = [v for v in div8 if all(x > 0 for x in v)]
        print(f"    all counts divisible by 8 (must be true): "
              f"{len(div8)}/{len(allvecs)}"
              f"{'  OK' if len(div8) == len(allvecs) else '  *** VIOLATION ***'}")
        print(f"    cycles touching ALL FIVE coordinates: {len(allpos)}")

        hits = []
        for v in sorted(allpos)[:4000]:
            e = admissible_from_vector(v, rho0)
            if e:
                hits.append((v, e))
        # also try pairwise sums of cycle vectors from the same SCC
        if not hits:
            pool = sorted(div8)[:120]
            for a, b in combinations_with_replacement(pool, 2):
                v = tuple(x + y for x, y in zip(a, b))
                e = admissible_from_vector(v, rho0)
                if e:
                    hits.append((v, e))
                    if len(hits) > 5:
                        break
        print(f"    cycle vectors proportional to an admissible speed vector: {len(hits)}")
        for v, e in hits[:5]:
            print(f"      cycle counts {v}  ->  speeds "
                  f"(e_1,e_3,e_5,e_7,e_{rho0}) = {e}")
        print()


if __name__ == "__main__":
    main()
