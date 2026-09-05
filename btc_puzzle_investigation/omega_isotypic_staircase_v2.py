#!/usr/bin/env sage
# omega_isotypic_staircase_v2 -- confirm the MECHANISM (why the fixed-target ideal breaks sigma) and
# that the well-posed TARGET-ORBIT ideal IS sigma-invariant. Exact GF(p). Characterization.
import sys, os, random as pyr
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from sage.all import *
from semaev_elimination_v1 import summation_poly, decomposition_system

def cube_root(F):
    for u in range(2, int(F.characteristic())):
        if F(u) != 1 and F(u)**3 == 1:
            return F(u)
    return None

def isotypic_split(I):
    g = {0: [], 1: [], 2: []}
    for mono in I.normal_basis():
        d = int(mono.degree()); g[d % 3].append(d)
    return {r: len(g[r]) for r in (0, 1, 2)}, {r: (max(g[r]) if g[r] else None) for r in (0, 1, 2)}

def main():
    p = 523; m = 3; F = GF(p); beta = cube_root(F)
    print(f"p={p} m={m} beta={beta}\n")

    # ---- (1) covariance weight kappa of the UNSPECIALIZED Semaev poly under x_i -> beta x_i ----
    S, zs, t = summation_poly(F, 0, 7, m)     # vars z1..zm, t
    Rbig = zs[0].parent()
    sigbig = Rbig.hom([beta * v for v in Rbig.gens()], Rbig)
    Ssig = sigbig(S)
    ratio = Ssig.lc() * S.lc()**(-1)           # exact GF(p) inverse; both scaled same iff Ssig=beta^k*S
    is_cov = (Ssig == ratio * S)
    kappa = None
    for k in range(3):
        if ratio == beta**k: kappa = k
    print(f"[covariance] S(beta z, beta t) == beta^k * S ? {is_cov}   ratio=beta^{kappa}  (kappa={kappa})")

    # ---- (2) mechanism: for a fixed target tval, sigma(Sx) should equal beta^kappa * S(z, beta^-1 tval) ----
    pyr.seed(1); E = EllipticCurve(F, [0, 7]); G = E.gens()[0]; N = int(E.order())
    pts = None
    while pts is None:
        cand = [int(pyr.randrange(1, N)) * G for _ in range(m)]
        xc = [P[0] for P in cand]
        if any(P == E(0) for P in cand) or len(set(xc)) < m: continue
        Ssum = E(0)
        for P in cand: Ssum = Ssum + P
        if -Ssum == E(0): continue
        pts = cand; tval = (-Ssum)[0]
    Rx, gens, xs = decomposition_system(F, 0, 7, m, tval, sorted({x for xx in xc for x in (xx, beta*xx, beta*beta*xx)}))
    Sx = gens[0]
    sigx = Rx.hom([beta * x for x in Rx.gens()], Rx)
    # S specialized at the beta^-1-rotated target:
    binv = beta**(-1)
    phi_rot = Rbig.hom(list(Rx.gens()) + [F(binv * tval)], Rx)
    Sx_rot = phi_rot(S)
    mech = (sigx(Sx) == (beta**kappa) * Sx_rot)
    print(f"[mechanism ] sigma(Sx) == beta^kappa * S(x, beta^-1 * tval) ? {mech}   "
          f"(sigma(Sx)==scalar*Sx ? {sigx(Sx) == (sigx(Sx).lc()*Sx.lc()**(-1))*Sx})")

    # ---- (3) TARGET-ORBIT ideal: keep target as a variable, add x_T^3 - tval^3 (mu3-orbit of target),
    #          mu3-invariant V field eqs -> the whole system is sigma-invariant. Check + isotypic split. ----
    R4 = PolynomialRing(F, ['x1', 'x2', 'x3', 'xT'], order='degrevlex')
    x1, x2, x3, xT = R4.gens()
    phi4 = Rbig.hom([x1, x2, x3, xT], R4)          # z_i -> x_i, t -> xT (UNspecialized)
    S4 = phi4(S)
    Vinv = sorted({x for xx in xc for x in (xx, beta*xx, beta*beta*xx)})
    fld = [prod([xi - F(r) for r in Vinv]) for xi in (x1, x2, x3)]
    torb = xT**3 - F(tval)**3                       # target mu3-orbit
    I4 = R4.ideal([S4] + fld + [torb])
    dim4 = int(I4.dimension())
    sig4 = R4.hom([beta * g for g in R4.gens()], R4)
    inv4 = all(I4.reduce(sig4(g)) == 0 for g in I4.gens())
    print(f"\n[target-orbit ideal] dim={dim4}  sigma_preserves_I={inv4}", end="")
    if dim4 == 0:
        d, tp = isotypic_split(I4)
        print(f"  quo={int(I4.vector_space_dimension())}  isotype_dims={d}  isotype_topdeg={tp}")
    else:
        print("  (positive-dim: the un-specialized relation variety; 0-dim needs more constraints)")

    # ---- (4) negative control fixed: a generic 0-dim ideal should read sigma_preserves=False ----
    set_random_seed(5)
    while True:
        Ig = R4.ideal([R4.random_element(degree=2, terms=Infinity) for _ in range(4)])
        if int(Ig.dimension()) == 0: break
    invg = all(Ig.reduce(sig4(g)) == 0 for g in Ig.gens())
    print(f"[neg control generic] quo={int(Ig.vector_space_dimension())}  sigma_preserves_I={invg}  (expect False)")

if __name__ == "__main__":
    main()
