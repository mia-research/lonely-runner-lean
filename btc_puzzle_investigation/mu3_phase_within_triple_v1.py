#!/usr/bin/env python3
"""
mu3_phase_within_triple_v1.py — runner for PREREG_mu3_phase_within_triple_v1.md.

Tests mu3 PHASE alignment within GLV triples of U(a0,b,c): the gauge-invariant real-part isotype
energy |R_w|^2 = Sum_j r_j^2 - Sum_{i<j} r_i r_j  (r_j = Re u_j),  |R_w|^2 = (1/2) Sum (r_i-r_j)^2.

Summed over triples, Sum_t |R_w|^2 = A2 - P, where P = Sum_{within-triple pairs} r_i r_j and A2=Sum_all r^2
is constant under repartition. So the Null-P (uniform repartition of reps into triples, keeping every
rep's complex U intact) z-score reduces to the standardized P — the EXACT phase analogue of the
validated magnitude Null-B, weighted by r. Closed-form moments (power sums A1..A4); no MC loop.
NORMALIZATION NOTE (only deviation from spec's per-triple-normalized psi): global vs per-triple
normalization does not change the Z (it cancels), only psi's descriptive scale; the tested object
(|R_w|^2 isotype energy) and gauge-invariance are identical. psi_mean reported descriptively.

r_j = Re(u_j) and |u_j| are invariant under the forced +- gauge u->conj(u), so the statistic is
gauge-invariant (verified in selftest). Exact-int point/index path; float carve-out only in U (analytic).

*** WARNING (2026-08-10): the analytic Null-P Z below is CORRECT PER BLOCK but WRONG WHEN POOLED. ***
The true mu3-grouping {b,beta b,beta^2 b} is shared across ALL (a0,c) blocks, so pooling per-block
variances as if blocks were independent UNDERESTIMATES Var(P_total) by ~2.85x and inflates the pooled
Z (the tell: pooled Z was ~constant +3.4 across a 10x range of N -- a variance artifact, not a signal).
The DECISION statistic is the empirical GLOBAL-repartition null in `mu3_phase_within_triple_globalnull_v2.py`
(one regrouping shared across all blocks): corrected pooled Stouffer = +1.88 < 3 (scoped null).
See RESULT_mu3_phase_within_triple_v1.md. The per-block Z here is retained only as a diagnostic.
"""
import sys, math, argparse, importlib.util
import numpy as np

_spec = importlib.util.spec_from_file_location(
    "mag", __file__.replace("mu3_phase_within_triple_v1.py", "mu3_glv_frequency_support_v1.py"))
mag = importlib.util.module_from_spec(_spec); _saved = sys.argv; sys.argv = ["x"]
_spec.loader.exec_module(mag); sys.argv = _saved

W3 = math.exp(2*math.pi/3)  # unused; keep numpy roots below
OM = np.exp(2j*np.pi/3)

def U_column(Warr, Xarr, Yarr, c, p):
    """complex U at index b: fft(g)[b] = U(a0,-b,c) = conj U(a0,b,c). Re and |.| are gauge-invariant."""
    ecy = np.exp(2j*np.pi*((c*Yarr) % p)/p)
    g = np.zeros(p, dtype=np.complex128)
    np.add.at(g, Xarr, Warr*ecy)
    return np.fft.fft(g)

def null_P_moments(r):
    """Exact E[P], Var[P] for P = sum_{within-triple pairs} r_i r_j under uniform repartition of the
    R=len(r) reps into R/3 triples of size 3. Power-sum closed form (validated vs MC in selftest)."""
    R = len(r)
    A1 = r.sum(); A2 = (r*r).sum(); A3 = (r**3).sum(); A4 = (r**4).sum()
    q1 = 2.0/(R-1)
    q2 = 2.0/((R-1)*(R-2))
    qd = 4.0/((R-1)*(R-2))
    SW = 0.5*(A1*A1 - A2)                       # sum_{i<j} r_i r_j
    W2 = 0.5*(A2*A2 - A4)                        # sum_{i<j} r_i^2 r_j^2
    Shared = (A1*A1 - A2)*A2 - 2*A1*A3 + 2*A4   # ordered shared-vertex sum
    Disjoint = SW*SW - W2 - Shared
    E_P = q1*SW
    E_P2 = q1*W2 + q2*Shared + qd*Disjoint
    return E_P, max(E_P2 - E_P*E_P, 0.0)

def P_obs(r, tri):
    """sum over TRUE triples of (r_i r_j + r_i r_k + r_j r_k)."""
    r0, r1, r2 = r[tri[:, 0]], r[tri[:, 1]], r[tri[:, 2]]
    return float((r0*r1 + r0*r2 + r1*r2).sum())

def run_curve_phase(p, a, b, n_areps, label, plant_frac=0.0, negative=False, rng=None, gauge_flip=False):
    p, n, G, X, Y, beta, lam = mag.setup_curve(p, a, b, want_lambda=True)
    reps, tri = mag.build_triples(p, beta)
    R = len(reps)
    areps = mag.a_reps(n, lam, n_areps)
    d = np.arange(1, n)
    P_tot = 0.0; E_tot = 0.0; V_tot = 0.0; psi_acc = []
    for a0 in areps:
        Warr = np.exp(2j*np.pi*a0*d/n)
        for c in range(1, p):
            Uc = U_column(Warr, X, Y, c, p)
            u = Uc[reps]                                   # complex U at +- reps
            if gauge_flip and rng is not None:             # random per-rep conjugation (gauge test)
                fl = rng.integers(0, 2, size=R).astype(bool); u = np.where(fl, np.conj(u), u)
            if negative:                                    # NEG control: ALL reps get iid random phase
                mags = np.abs(u); u = mags*np.exp(1j*rng.uniform(0, 2*np.pi, size=R))
            elif plant_frac > 0.0:                           # PLANT: frac of TRUE triples mu3-aligned
                ntr = tri.shape[0]; npl = int(round(plant_frac*ntr))
                sel = rng.choice(ntr, size=npl, replace=False)
                mags = np.abs(u)
                for t in sel:
                    idx = tri[t]
                    phi = rng.uniform(0, 2*np.pi)
                    u[idx] = mags[idx]*np.exp(1j*(phi + 2*np.pi*np.arange(3)/3))
            r = np.real(u)
            Pb = P_obs(r, tri)
            Eb, Vb = null_P_moments(r)
            P_tot += Pb; E_tot += Eb; V_tot += Vb
            # descriptive psi (per-triple normalized)
            mag2 = (np.abs(u))**2
            num = 0.5*((r[tri[:,0]]-r[tri[:,1]])**2 + (r[tri[:,1]]-r[tri[:,2]])**2 + (r[tri[:,2]]-r[tri[:,0]])**2)
            den = mag2[tri].sum(axis=1)
            m = den > 0
            if m.any(): psi_acc.append(float(np.median(num[m]/den[m])))
    Z = -(P_tot - E_tot)/math.sqrt(V_tot) if V_tot > 0 else 0.0   # + => mu3-phase-aligned
    return {"label": label, "p": p, "n": n, "R": R, "Z": Z,
            "psi_med": float(np.median(psi_acc)) if psi_acc else float('nan')}

def selftest():
    p, a, b = 61, 0, 7
    pp, n, G, X, Y, beta, lam = mag.setup_curve(p, a, b)
    reps, tri = mag.build_triples(p, beta); R = len(reps)
    print(f"[selftest] F_{p} n={n} beta={beta} R={R} triples={tri.shape[0]}")
    d = np.arange(1, n); Warr = np.exp(2j*np.pi*1*d/n)
    u = U_column(Warr, X, Y, 3, p)[reps]; r = np.real(u)
    # (i) analytic Null-P moments vs empirical repartition MC
    rng = np.random.default_rng(0); emp = []
    for _ in range(30000):
        perm = rng.permutation(R).reshape(-1, 3)
        r0, r1, r2 = r[perm[:,0]], r[perm[:,1]], r[perm[:,2]]
        emp.append(float((r0*r1+r0*r2+r1*r2).sum()))
    emp = np.array(emp); E, V = null_P_moments(r)
    se_mean = math.sqrt(emp.var()/len(emp))               # MC standard error on the mean
    okm = abs(E-emp.mean()) < 5*se_mean and abs(V-emp.var()) < 0.10*max(V, 1)
    print(f"[selftest] (i) Null-P analytic E={E:.4f} Var={V:.4f} | MC E={emp.mean():.4f} Var={emp.var():.4f} ok={okm}")
    # (ii) gauge invariance: flip each rep's conjugation -> P_obs and psi unchanged
    Pf = P_obs(np.real(np.conj(u)), tri)
    print(f"[selftest] (ii) gauge flip (u->conj u) P_obs delta = {abs(Pf-P_obs(r,tri)):.2e}  ok={abs(Pf-P_obs(r,tri))<1e-6}")
    # (iii) plant fires, negative flat (single prime)
    rng = np.random.default_rng(1)
    zp = run_curve_phase(61, 0, 7, 8, "PLANT", plant_frac=0.10, rng=rng)["Z"]
    zn = run_curve_phase(61, 0, 7, 8, "NEG", plant_frac=0.10, negative=True, rng=rng)["Z"]
    z0 = run_curve_phase(61, 0, 7, 8, "RAW", rng=rng)["Z"]
    zg = run_curve_phase(61, 0, 7, 8, "GAUGE", rng=rng, gauge_flip=True)["Z"]
    print(f"[selftest] (iii) plant Z={zp:+.2f} (fire) | neg Z={zn:+.2f} (flat) | raw Z={z0:+.2f} | gauge-flip Z={zg:+.2f} (==raw)")
    ok = okm and abs(Pf-P_obs(r,tri)) < 1e-6 and zp > 5 and abs(zn) < 4 and abs(zg-z0) < 1e-6
    print(f"[selftest] PASS={ok}")
    return ok

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--primes", default="")
    ap.add_argument("--areps", type=int, default=24)
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--seed", type=int, default=12345)
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    rng = np.random.default_rng(args.seed)
    primes = [int(x) for x in args.primes.split(",") if x]
    zlist = []
    for p in primes:
        r = run_curve_phase(p, 0, 7, args.areps, f"CM p={p}")
        zlist.append(r["Z"])
        print(f"[{r['label']}] n={r['n']} R={r['R']}  Z={r['Z']:+.3f}  psi_med={r['psi_med']:.4f}", flush=True)
        if args.controls and p == primes[0]:
            zp = run_curve_phase(p, 0, 7, args.areps, "PLANT", plant_frac=0.05, rng=rng)["Z"]
            zn = run_curve_phase(p, 0, 7, args.areps, "NEG", plant_frac=0.05, negative=True, rng=rng)["Z"]
            print(f"[CONTROL plant  ] Z={zp:+.3f} (must FIRE >> 0)", flush=True)
            print(f"[CONTROL negative] Z={zn:+.3f} (must stay ~0)", flush=True)
    if len(zlist) > 1:
        print(f"[POOLED] Stouffer Z = {sum(zlist)/math.sqrt(len(zlist)):+.3f} over {len(zlist)} primes", flush=True)
