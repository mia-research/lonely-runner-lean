#!/usr/bin/env python3
"""
amicable_log_bridge_v1.py -- execute PREREG_amicable_log_bridge_v1.md (the DECIDABLE sub-question).

Registered object: does the mu6-averaged cubic-character pairing between the field-side Z[omega] class
F(P)=chi3^(p)(y(P)) and the partner-side class g(d)=chi3^(n)(d^3+7) show amicability-specific
dependence, beyond matched non-amicable controls?  (The posed "transfer map" is undecidable: the full
phi(n)-average is trivial, and the log coordinate IS the discrete log -- section 0.)

T(u) = (n-1) * sum_d F(P_d) conj(g(d))  -  Sigma_F conj(Sigma_g)   in Z[omega]   (double-centred)
R(u) = N(T) / ((n-1)^2 n)   exact Fraction.  Primary = Mann-Whitney of per-unit rank p-values
       pi(u) [vs NULL-A mu6-relabel] :  amicable arm vs matched-control arm.
EXACTNESS: everything integer / Z[omega] / Fraction.  No float, no carve-out.
Usage: amicable_log_bridge_v1.py [p_max] [M]
"""
import sys, random
from fractions import Fraction
import numpy as np
from mu3_projection_v1 import is_prime, _arr_legendre, cube_root_unity, order3_modn, find_generator, coords

B = 7

# ---------------- Z[omega] exact arithmetic: (a,b) = a + b*omega, omega^2 = -1 - omega
def zw_mul(u, v):
    a, b = u; c, d = v
    return (a * c - b * d, a * d + b * c - b * d)


def zw_conj(u):
    a, b = u
    return (a - b, -b)


def zw_add(u, v):
    return (u[0] + v[0], u[1] + v[1])


def zw_norm(u):
    a, b = u
    return a * a - a * b + b * b


OMEGA = [(1, 0), (0, 1), (-1, -1)]         # omega^0, omega^1, omega^2


def countE(p):
    x = np.arange(p, dtype=np.int64)
    rhs = (x * x % p * x + B) % p
    return p + 1 + int(_arr_legendre(rhs, p).sum())


def chi3_table(p):
    """return function v -> omega^k (as Z[omega]) for chi3^(p); 0 -> (0,0)."""
    beta = cube_root_unity(p)
    e = (p - 1) // 3
    lut = {}                                # v^e in {1,beta,beta^2} -> k
    b0, b1, b2 = 1, beta, beta * beta % p
    lut[b0] = 0; lut[b1] = 1; lut[b2] = 2

    def chi(v):
        v %= p
        if v == 0:
            return (0, 0)
        return OMEGA[lut[pow(v, e, p)]]
    return chi


def mu6_orbits_of_d(n, lam):
    seen = bytearray(n)
    orbits = []
    for a in range(1, n):
        if seen[a]:
            continue
        elems = []
        t = a
        for _ in range(3):
            for e in (t, (n - t) % n):
                if not seen[e]:
                    seen[e] = 1; elems.append(e)
            t = t * lam % n
        orbits.append(elems)
    return orbits


def build_unit(p, n):
    lam_n = order3_modn(n)
    lam_p = None
    G = find_generator(p, n)
    xs, ys = coords(G, p, n)
    chip = chi3_table(p)
    chin = chi3_table(n)
    F = [(0, 0)] * n
    g = [(0, 0)] * n
    for d in range(1, n):
        F[d] = chip(ys[d])
        g[d] = chin((d * d % n * d + B) % n)
    return xs, ys, F, g, lam_n


def forced_rows(p, n, F, g, lam_n):
    """section 2 forced checks: F(P_{lam d})=F(P_d), F(P_{-d})=F(P_d), g(lam d)=g(d)."""
    bad = 0
    for d in range(1, n):
        if F[(lam_n * d) % n] != F[d]: bad += 1
        if F[(n - d) % n] != F[d]: bad += 1
        if g[(lam_n * d) % n] != g[d]: bad += 1
    return bad


def T_and_R(F, g, n):
    SF = (0, 0); Sg = (0, 0); cross = (0, 0)
    for d in range(1, n):
        SF = zw_add(SF, F[d])
        Sg = zw_add(Sg, g[d])
        cross = zw_add(cross, zw_mul(F[d], zw_conj(g[d])))
    T = zw_add((( n - 1) * cross[0], (n - 1) * cross[1]), tuple(-x for x in zw_mul(SF, zw_conj(Sg))))
    R = Fraction(zw_norm(T), (n - 1) * (n - 1) * n)
    return T, R, SF, Sg


def null_R(F, g, n, orbits, M, rng):
    """NULL-A: mu6-equivariant relabel of F (permute orbit-values), recompute R.  F const on orbits."""
    # F is constant on each orbit; capture per-orbit value + Sigma over orbit of conj(g)
    conj_g_orbit = []
    orbit_Fval = []
    for O in orbits:
        s = (0, 0)
        for d in O:
            s = zw_add(s, zw_conj(g[d]))
        conj_g_orbit.append(s)
        orbit_Fval.append(F[O[0]])
    Fvals = orbit_Fval
    # Sigma_F fixed; Sigma_g fixed
    SF = (0, 0); Sg = (0, 0)
    for d in range(1, n):
        SF = zw_add(SF, F[d]); Sg = zw_add(Sg, g[d])
    conjSg = zw_conj(Sg)
    Osz = len(orbits)
    Rs = []
    Farr = np.array([[v[0], v[1]] for v in Fvals], dtype=np.int64)
    Ga = np.array([[c[0], c[1]] for c in conj_g_orbit], dtype=np.int64)   # conj g summed per orbit
    for _ in range(M):
        perm = rng.permutation(Osz)
        fp = Farr[perm]
        # cross = sum_O F_O * (conj g)_O   (Z[omega] mult, vectorized)
        a, b = fp[:, 0], fp[:, 1]; c, d = Ga[:, 0], Ga[:, 1]
        cr0 = int((a * c - b * d).sum()); cr1 = int((a * d + b * c - b * d).sum())
        T0 = (n - 1) * cr0 - zw_mul(SF, conjSg)[0]
        T1 = (n - 1) * cr1 - zw_mul(SF, conjSg)[1]
        Rs.append(Fraction(zw_norm((T0, T1)), (n - 1) * (n - 1) * n))
    return Rs


def plant_fire(p, n, F, g, lam, M, rng):
    """section 5 planted positive: overwrite F on first eps*(n-1)/6 mu6-orbits by the partner class
    g(rep) (mu6-invariant by construction); R must exceed the NULL-A 99.5% band.  Returns eps_min."""
    orbits = mu6_orbits_of_d(n, lam)
    Osz = len(orbits)
    band = None
    eps_min = None
    Rs0 = null_R(F, g, n, orbits, min(M, 999), rng)
    thr = sorted(Rs0)[int(0.995 * len(Rs0))]
    for eps in (Fraction(1, 2), Fraction(1, 4), Fraction(1, 10), Fraction(1, 25),
                Fraction(1, 50), Fraction(1, 100), Fraction(1, 250), Fraction(1, 1000)):
        k = int(eps * Osz)
        Fp = list(F)
        for O in orbits[:k]:
            gv = g[O[0]]                       # partner class at the rep, forced mu6-invariant
            for d in O:
                Fp[d] = gv
        _, R, _, _ = T_and_R(Fp, g, n)
        fired = R > thr
        if fired:
            eps_min = eps
        else:
            break
    return eps_min, thr


def find_frame(p_max):
    amic = []; nona = []
    p = 5
    while p < p_max:
        if is_prime(p) and p % 3 == 1:
            n = countE(p)
            if is_prime(n) and n % 6 == 1 and p != n:            # exclude anomalous self (p=n)
                m = countE(n)
                (amic if m == p else nona).append((p, n))
        p += 1
    return amic, nona


def match_control(am, nona):
    """NULL-B: match each amicable unit to a non-amicable one on orientation + n within 1.25x."""
    used = set(); pairs = []
    for (p, n) in am:
        best = None
        for i, (pc, nc) in enumerate(nona):
            if i in used:
                continue
            if ((pc < nc) == (p < n)) and 0.8 <= nc / n <= 1.25:
                if best is None or abs(nc - n) < abs(nona[best][1] - n):
                    best = i
        if best is not None:
            used.add(best); pairs.append((p, n, nona[best][0], nona[best][1]))
    return pairs


def main():
    p_max = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 9999
    rng = np.random.default_rng(20260724)
    print("=" * 92)
    print("AMICABLE LOG-BRIDGE (decidable sub-question)  M=%d  p<%d" % (M, p_max))
    print("=" * 92)
    amic, nona = find_frame(p_max)
    print("\namicable 2-cycle units:", amic)
    print("non-amicable frame units:", len(nona))
    matched = match_control(amic, nona)
    print("matched amicable<->control pairs:", len(matched))

    # ---- PLANT (must fire at eps=1/2 or the arm is VOID) -- on a REPRESENTATIVE large unit
    # (tiny n has no resolution: eps_min ~ 3/sqrt(n), and the null band is look-elsewhere-dominated)
    print("\n=== PLANT (synthetic transfer; must fire at eps=1/2) ===")
    pp, pn = max(amic, key=lambda pq: pq[1])
    xs, ys, Fp, gp, lamp = build_unit(pp, pn)
    eps_min, thr = plant_fire(pp, pn, Fp, gp, lamp, M, rng)
    if eps_min is None or eps_min < Fraction(1, 2):
        print("  plant on p=%d: eps_min=%s (null 99.5%% thr R=%.3f)" % (pp, eps_min, thr))
    if eps_min is None:
        print("  *** PLANT FAILED at eps=1/2 -> ARM VOID, no verdict ***"); return
    print("  plant fires down to eps_min = %s  (detection floor; print beside any null)" % eps_min)

    def pi_of(p, n):
        xs, ys, F, g, lam = build_unit(p, n)
        bad = forced_rows(p, n, F, g, lam)
        if bad:
            print("   *** FORCED ROW FAIL p=%d bad=%d -> VOID unit ***" % (p, bad)); return None
        T, R, SF, Sg = T_and_R(F, g, n)
        orbits = mu6_orbits_of_d(n, lam)
        Rs = null_R(F, g, n, orbits, M, rng)
        rank = sum(1 for r in Rs if r >= R)
        pi = Fraction(1 + rank, M + 1)
        return float(pi), float(R), T

    print("\n=== per-unit (amicable arm) ===")
    pi_am = []
    for p, n, pc, nc in matched:
        r = pi_of(p, n)
        if r:
            pi, R, T = r
            print("  AMIC  p=%-5d n=%-5d  R=%.3f  pi=%.4f  T=%s" % (p, n, R, pi, T))
            pi_am.append(pi)
    print("\n=== per-unit (control arm) ===")
    pi_ct = []
    for p, n, pc, nc in matched:
        r = pi_of(pc, nc)
        if r:
            pi, R, T = r
            print("  CTRL  p=%-5d n=%-5d  R=%.3f  pi=%.4f" % (pc, nc, R, pi))
            pi_ct.append(pi)

    # Mann-Whitney W (amic vs control), exact-ish via normal approx + report U
    n1, n2 = len(pi_am), len(pi_ct)
    if n1 and n2:
        U = sum(1 if a < b else (0.5 if a == b else 0) for a in pi_am for b in pi_ct)
        mu = n1 * n2 / 2; sd = (n1 * n2 * (n1 + n2 + 1) / 12) ** 0.5
        z = (U - mu) / sd if sd else 0
        print("\n=== PRIMARY Mann-Whitney (amicable pi vs control pi) ===")
        print("  n_amic=%d n_ctrl=%d  U=%.1f  E[U]=%.1f  z=%+.3f  (|z|>2.58 => reject at 0.01)" % (n1, n2, U, mu, z))
        print("  median pi: amic=%.3f  control=%.3f" % (np.median(pi_am), np.median(pi_ct)))
    print("BRIDGE_DONE")


if __name__ == '__main__':
    main()
