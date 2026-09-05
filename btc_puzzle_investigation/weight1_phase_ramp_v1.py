#!/usr/bin/env python3
"""
weight1_phase_ramp_v1.py -- execute PREREG_weight1_phase_ramp_v1.md (Brick C).
Public per-point mu6-BROKEN phase Phi(d)=arg(sum w_{j,s} A_{j,s}(P_d)); test d-linear alignment to a*d.

Signal path exact int/Fraction (point arith, eis, chi2). Float carve-out: zeta3/exp/arg in A_{j,s}/Phi/S
ONLY (downstream, never feeds back). d never in the Phi path.
First: the ADMISSIBILITY GATE (does oblique M break mu6?) -- run before the statistic.
Usage: weight1_phase_ramp_v1.py [gate|run] [p ...]
"""
import sys, cmath, math, random
from fractions import Fraction
from int1_frame_operator_v1 import build
from mu3_projection_v1 import count_E, is_prime, cube_root_unity, find_generator, coords

Bc = 7
Z3 = cmath.exp(2j*cmath.pi/3)
# oblique projector weights over isotypes (j in {0,1,2}, s in {0,1})
W = {(1,1):1.0, (0,0):0.0, (0,1):0.0, (2,0):0.25, (1,0):0.25, (2,1):0.25}
W_PURE = {(1,1):1.0, (0,0):0.0, (0,1):0.0, (2,0):0.0, (1,0):0.0, (2,1):0.0}  # pure (1,1) = mu6-COVARIANT ctrl (G~0)


def chi2(v, p): return 0 if v % p == 0 else (1 if pow(v % p, (p-1)//2, p) == 1 else -1)


def phi0_of(xcoord, chi2y, eis):
    """phi0(Q)=u + i*chi2(y)*v, (u,v)=eis(x). Returns complex (u,v exact -> float here, carve-out)."""
    u, v = eis(xcoord)
    return float(u) + 1j*chi2y*float(v)


def A_isotypes(x, y, p, beta, eis):
    """A_{j,s}(P) for j in 0,1,2 ; s in 0,1.  Orbit: phi^m (x->beta^m x), [-1]^t (y->(-1)^t y)."""
    chi2y = chi2(y, p); chi2m1 = chi2((p-1), p)     # chi2(-1)
    xm = [x, beta*x % p, beta*beta % p*x % p]        # beta^m x
    # phi0 at (m,t): u,v from eis(beta^m x); chi2((-1)^t y) = chi2(-1)^t * chi2(y)
    ph = {}
    for m in range(3):
        u, v = eis(xm[m])
        for t in range(2):
            c2 = (chi2m1**t)*chi2y
            ph[(m,t)] = float(u) + 1j*c2*float(v)
    A = {}
    for j in range(3):
        for s in range(2):
            acc = 0j
            for m in range(3):
                for t in range(2):
                    acc += (Z3**(-j*m))*((-1)**(-s*t))*ph[(m,t)]
            A[(j,s)] = acc
    return A


def Phi_of(x, y, p, beta, eis, w):
    A = A_isotypes(x, y, p, beta, eis)
    z = sum(w[k]*A[k] for k in w)
    return cmath.phase(z), abs(z)


def setup(p):
    n = count_E(p); assert is_prime(n), "n not prime"
    beta = cube_root_unity(p); G = find_generator(p, n); xs, ys = coords(G, p, n)
    eis, eps = build(p)
    return n, beta, G, xs, ys, eis


def gate(p):
    """G = mean over mu6-orbits of CircVar({Phi(g P) - l(g)}), l = (1,1)-covariant ramp 120m+180t deg."""
    n, beta, G, xs, ys, eis = setup(p)
    # collect one point per mu6 orbit (scalar orbit {+-lam^j d}); reuse mu3 lam
    lam = next(c for c in range(2, n) if c != 1 and pow(c, 3, n) == 1)
    seen = bytearray(n); reps = []
    for d in range(1, n):
        if seen[d]: continue
        orb = set(); t = d
        for _ in range(3):
            orb.add(t); orb.add((n-t) % n); t = t*lam % n
        for o in orb: seen[o] = 1
        reps.append(sorted(orb))
    def circvar(phases):
        z = sum(cmath.exp(1j*a) for a in phases)/len(phases)
        return 1 - abs(z)
    for wname, w in (("OBLIQUE", W), ("PURE(1,1) covariant ctrl", W_PURE)):
        gs = []
        for orb in reps[:400]:
            # the 6 orbit points: for scalar d0=orb-min, the group elements give x=beta^m x_{d0}, y=+-y
            d0 = orb[0]; x0, y0 = xs[d0], ys[d0]
            phases = []
            for m in range(3):
                xm = pow(beta, m, p)*x0 % p
                for tt in range(2):
                    yv = y0 if tt == 0 else (p-y0) % p
                    ph, _ = Phi_of(xm, yv, p, beta, eis, w)
                    ell = math.radians(120*m + 180*tt)
                    phases.append((ph - ell))
            gs.append(circvar(phases))
        G_ = sum(gs)/len(gs)
        print("  p=%d (p%%4=%d,p%%12=%d) %-22s  G=%.4f  -> %s"
              % (p, p%4, p%12, wname, G_, "BREAKS mu6 (PASS)" if (wname.startswith("OBL") and G_>=0.05)
                 else ("covariant~0 (ctrl ok)" if wname.startswith("EQ") and G_<0.05 else
                       ("FAIL" if wname.startswith("OBL") else "ctrl-unexpected"))))


def run_prime(p, B=2000, seed=0):
    """S_p=|R_p(1)|; permutation (d-label) null preserving {Phi(d)}; plant must fire.
    Admissible only at p%4==3 (else A_{1,1}=0, degenerate). Returns dict."""
    n, beta, G, xs, ys, eis = setup(p)
    Phi = [0.0]*n
    degen = 0
    for d in range(1, n):
        ph, mag = Phi_of(xs[d], ys[d], p, beta, eis, W)
        if mag < 1e-12: degen += 1
        Phi[d] = ph
    D = list(range(1, n))
    def Sstat(phi, dl):   # |mean exp(i(phi_d - 2pi a d/n))|, a=1
        z = sum(cmath.exp(1j*(phi[d] - 2*cmath.pi*d/n)) for d in dl)/len(dl)
        return abs(z)
    Sobs = Sstat(Phi, D)
    rng = random.Random(seed); ge = 0
    for _ in range(B):
        pr = D[:]; rng.shuffle(pr)
        # permute the Phi<->d pairing: Phi values reassigned to shuffled d-order
        phi_perm = {D[i]: Phi[pr[i]] for i in range(len(D))}
        if Sstat(phi_perm, D) >= Sobs: ge += 1
    pperm = (1+ge)/(B+1)
    # PLANT (must fire): Phi*(d)=2pi d/n
    Sp = Sstat([0.0]+[2*cmath.pi*d/n for d in range(1,n)], D)
    return dict(p=p, n=n, degen=degen, S=Sobs, pperm=pperm, plant_S=Sp)


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'gate'
    ps = [int(x) for x in sys.argv[2:]] or [163, 349]
    if mode == 'gate':
        print("=== ADMISSIBILITY GATE (oblique M must break mu6: G>=0.05; pure-(1,1) ctrl ~0) ===")
        for p in ps:
            if p % 3 != 1 or Bc % p == 0: print("  p=%d skip"%p); continue
            gate(p)
    elif mode == 'run':
        secp_class = [p for p in ps if p % 12 == 7]
        print("=== RUN (secp class p%%12=7 only; p%%12=1 INADMISSIBLE: A_{1,1}=0 degenerate) ===")
        lnps = []
        for p in secp_class:
            r = run_prime(p)
            lnps.append(math.log(r['pperm']))
            print("  p=%-5d n=%-5d  S=%.4f  p_perm=%.4f  degen(A~0)=%d  PLANT S=%.3f(%s)"
                  %(r['p'],r['n'],r['S'],r['pperm'],r['degen'],r['plant_S'],
                    "fires" if r['plant_S']>0.9 else "*** PLANT FAIL ***"))
        X = -2*sum(lnps); dof = 2*len(secp_class)
        print("  FISHER X=%.2f  dof=%d  (chi2 .99 = %.1f) -> %s"
              %(X, dof, {2:9.2,4:13.3,6:16.8,8:20.1,10:23.2}.get(dof,dof*1.4),
                "LEAK" if X > {2:9.2,4:13.3,6:16.8,8:20.1,10:23.2}.get(dof,dof*1.4) else "bounded null"))
