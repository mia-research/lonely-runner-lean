#!/usr/bin/env sage
# omega_isotypic_staircase_v1 -- EXPLORATORY characterization (not a scored verdict).
# Question (RESULT_mu6_solving_degree follow-up #1): is the mu3-graded / omega-isotypic staircase
# a well-posed, NON-trivial, CM-specific object for the j0 Semaev decomposition ideal -- or is it
# trivial (diagonal grading = degree mod 3, curve-blind) or ill-posed (fixed target breaks sigma)?
# Reuses semaev_elimination_v1. Exact GF(p) throughout (no float in signal path).
import sys, os, random as pyr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sage.all import *
from semaev_elimination_v1 import decomposition_system

def cube_root(F):
    for u in range(2, int(F.characteristic())):
        if F(u)**3 == 1 and F(u) != 1:
            return F(u)
    return None

def isotypic_split(I, beta):
    """0-dim I: normal (standard-monomial) basis grouped by total-degree mod 3 = sigma-isotype."""
    nb = I.normal_basis()
    g = {0: [], 1: [], 2: []}
    for mono in nb:
        d = int(mono.degree()); g[d % 3].append(d)
    dims = {r: len(g[r]) for r in (0, 1, 2)}
    tops = {r: (max(g[r]) if g[r] else None) for r in (0, 1, 2)}
    return dims, tops

def sigma_preserves(I, Rx, gens, beta):
    """sigma: x_i -> beta x_i. Field-eqs (x_i^3 forms for mu3-inv V) are sigma-invariant; the test is
    whether sigma(Sx) reduces to 0 mod I (=> I sigma-stable => clean isotypic action on R/I)."""
    sig = Rx.hom([beta * x for x in Rx.gens()], Rx)
    Sx = gens[0]
    return (I.reduce(sig(Sx)) == 0)

def analyze(F, tval, V, m, beta, label):
    Rx, gens, xs = decomposition_system(F, 0, 7, m, tval, V)
    I = Rx.ideal(gens)
    dim = int(I.dimension())
    if dim != 0:
        print(f"  [{label:16}] |V|={len(V):2}  dim={dim}  (not 0-dim; skip)"); return None
    quo = int(I.vector_space_dimension())
    inv = sigma_preserves(I, Rx, gens, beta)
    dims, tops = isotypic_split(I, beta)
    print(f"  [{label:16}] |V|={len(V):2}  quo={quo:3}  sigma_preserves_I={inv!s:5}  "
          f"isotype_dims={dims}  isotype_topdeg={tops}")
    return dict(quo=quo, sigma_inv=inv, dims=dims, tops=tops)

def mu3inv_V(F, m, beta, seed, k):
    pyr.seed(int(seed)); E = EllipticCurve(F, [0, 7]); G = E.gens()[0]; N = int(E.order()); pchar = int(F.characteristic())
    for _ in range(400):
        pts = [int(pyr.randrange(1, N)) * G for _ in range(m)]; xc = [P[0] for P in pts]
        if any(P == E(0) for P in pts) or len(set(xc)) < m: continue
        S = E(0)
        for P in pts: S = S + P
        if -S == E(0): continue
        V = set()
        for x in xc: V |= {x, beta * x, beta * beta * x}
        while len(V) < 3 * k: r = F(pyr.randrange(1, pchar)); V |= {r, beta * r, beta * beta * r}
        return (-S)[0], sorted(V), xc
    return None

def random_V(F, m, seed, size):
    pyr.seed(int(seed) + 9999); E = EllipticCurve(F, [0, 7]); G = E.gens()[0]; N = int(E.order()); pchar = int(F.characteristic())
    for _ in range(400):
        pts = [int(pyr.randrange(1, N)) * G for _ in range(m)]; xc = [P[0] for P in pts]
        if any(P == E(0) for P in pts) or len(set(xc)) < m: continue
        S = E(0)
        for P in pts: S = S + P
        if -S == E(0): continue
        V = set(xc)
        while len(V) < size: V.add(F(pyr.randrange(0, pchar)))
        return (-S)[0], sorted(V), xc
    return None

def firing_controls(F, m, beta):
    """CTRL-SYM: a manifestly sigma-invariant 0-dim ideal (x_i^3 - c_i) -> known isotypic split of the
    27-dim quotient {x^a : 0<=a_i<=2}. CTRL-ASYM: a generic ideal that is NOT sigma-invariant."""
    Rx = PolynomialRing(F, ['x%d' % i for i in range(1, m + 1)], order='degrevlex')
    xr = Rx.gens()
    # CTRL-SYM
    Isym = Rx.ideal([xr[i]**3 - F(2 + i) for i in range(m)])
    sig = Rx.hom([beta * x for x in xr], Rx)
    inv_sym = all(Isym.reduce(sig(g)) == 0 for g in Isym.gens())
    dsym, tsym = isotypic_split(Isym, beta)
    print(f"  [CTRL-SYM x^3-c ]  quo={int(Isym.vector_space_dimension()):3}  sigma_preserves_I={inv_sym!s:5}  "
          f"isotype_dims={dsym}  isotype_topdeg={tsym}")
    # CTRL-ASYM (generic dense, should NOT be sigma-invariant)
    set_random_seed(11)
    Iasym = Rx.ideal([Rx.random_element(degree=3, terms=Infinity) for _ in range(m)] + [xr[i]**4 - F(1) for i in range(m)])
    if int(Iasym.dimension()) == 0:
        inv_a = all(Iasym.reduce(sig(g)) == 0 for g in Iasym.gens())
        print(f"  [CTRL-ASYM dense]  quo={int(Iasym.vector_space_dimension()):3}  sigma_preserves_I={inv_a!s:5}  "
              f"(expect False -- the discriminator distinguishes symmetric from generic)")
    else:
        print(f"  [CTRL-ASYM dense]  dim={int(Iasym.dimension())} (not 0-dim; control inconclusive, retry)")

def main():
    p = 523; m = 3
    F = GF(p); beta = cube_root(F)
    print(f"omega-isotypic staircase probe  p={p} m={m} beta={beta} (beta^3={beta**3})")
    print("\n[FIRING CONTROLS]")
    firing_controls(F, m, beta)
    print("\n[REAL SYSTEMS] j0 curve y^2=x^3+7, decomposable targets, mu3-invariant V vs random V:")
    for seed in (1, 2, 3, 4):
        r = mu3inv_V(F, m, beta, seed, k=2)
        if r: analyze(F, r[0], r[1], m, beta, f"mu3inv seed{seed}")
        rr = random_V(F, m, seed, size=9)
        if rr: analyze(F, rr[0], rr[1], m, beta, f"random seed{seed}")
    print("\n[done]")

if __name__ == "__main__":
    main()
