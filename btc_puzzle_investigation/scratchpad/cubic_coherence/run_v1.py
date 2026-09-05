#!/usr/bin/env python3
"""
run_v1.py — executes PREREG_subrayleigh_cubic_coherence_v1 (frozen).
Signal path is exact int (signal_path_v1). Float carve-out: root tables, transform, ensemble draws, z.
Primary: coherence-matched max-entropy magnitude null (importance-reweighting fallback form, since the
2% rejection acceptance is ~1/4000 << 1/500 -> the spec-declared fallback is used and RECORDED).
"""
import numpy as np
import sys, json, time
import signal_path_v1 as sp

SCHEDULE = [(151,133),(193,219),(211,199),(241,259),(277,273),(349,313),(397,397),
            (433,397),(523,489),(619,669),(691,651),(823,829),(937,973),(1093,1137),
            (1249,1303),(1471,1501),(1693,1729),(1987,2037),(2281,2203),(2671,2569),
            (3169,3073),(3607,3577),(4177,4303),(4861,4771),(5647,5529),(6571,6411),
            (7639,7699),(8893,9037),(10357,10173),(12043,12261)]

def build_T(p, n, X, weight_idx):
    """T(b)=sum_x A(x) e_p(+b x), A(x)=sum_{d:x_d=x} zeta_n^{weight_idx[d]}. Returns length-p complex."""
    en = np.exp(2j*np.pi*np.arange(n)/n)
    A = np.zeros(p, dtype=np.complex128)
    W = en[weight_idx]                       # weight per d
    np.add.at(A, np.asarray(X, dtype=np.int64), W)   # A[x_d] += W[d]; X[0]=0,W[0]=0 harmless (idx0 sentinel)
    # subtract the d=0 sentinel contribution (weight_idx[0] chosen 0 -> en[0]=1 added at x=0): remove it
    A[0] -= en[weight_idx[0]]
    return np.fft.ifft(A) * p                # e^{+2pi i b x/p}

def gauss_sum(p, chi):
    ep = np.exp(2j*np.pi*np.arange(p)/p)
    return np.sum(chi * ep)                   # tau = sum_t chi2(t) e_p(t)

def analyze(p, n, X, facs, rng, N0=40000, chunk=2000, verbose=True):
    a0 = 1
    idx_char = (a0*np.arange(n)) % n          # weight_idx for the character; idx_char[0]=0 sentinel
    T = build_T(p, n, X, idx_char)
    absT = np.abs(T)
    chi_full = np.array(sp.chi2_legendre(p))  # length p, chi[0]=0
    # slice b=1..p-1
    Tb = T[1:]; absTb = absT[1:]; chi = chi_full[1:]
    theta = np.angle(Tb)
    a_coef = chi * np.exp(3j*theta)           # a(b), b=1..p-1
    tau = gauss_sum(p, chi_full); u = tau/np.abs(tau)
    C_char = np.sum(chi * Tb**3)
    L1_char = absTb.sum()
    E_meas = (absTb**2).sum(); E_exact = sp.slice_L2_anchor(p, n)
    # moment ladder / shape of the slice magnitude multiset (why super/sub-Rayleigh)
    cv_char = absTb.std()/absTb.mean()          # Rayleigh CV = sqrt((4-pi)/pi) = 0.5227
    maxT_sqp = absTb.max()/np.sqrt(p)           # Weil ceiling ~4

    # ---- pair-rep structure (b and p-b), reps = 1..(p-1)//2 ----
    nreps = (p-1)//2
    reps = np.arange(1, nreps+1)              # b values
    par = p - reps                            # p-b
    # a(b)+a(p-b) over reps:
    a_rep = a_coef[reps-1]; a_par = a_coef[par-1]
    A2 = a_rep + a_par                        # coefficient multiplying rho_rep^3 in the cubic sum
    absT_rep = absTb[reps-1]                  # |T(b)| on reps (= |T(p-b)|)

    # ---- P-DIR ----
    exp_u = 1.0 if p % 4 == 1 else 1j
    pdir_u_ok = abs(u - exp_u) < 1e-6
    reC = np.real(np.conj(u)*C_char)
    magC = abs(C_char); magbound = np.sqrt(p)*n*n
    pdir_mag_ok = (0.4*magbound <= magC <= 1.6*magbound)
    pdir = pdir_u_ok and (reC > 0) and pdir_mag_ok

    # ---- P-COH (|C_char| >= sqrt(n)*median|C_MCHP| over 5 draws) ----
    Cs = []
    for _ in range(5):
        perm = np.arange(n)
        # permute respecting +-d pairing: build a permutation sigma with sigma(n-d)=-sigma(d)
        half = [d for d in range(1, n) if d < n-d]
        vals = list(range(1, len(half)+1))
        rng.shuffle(vals)
        sig = np.zeros(n, dtype=np.int64)
        for d, v in zip(half, vals):
            sig[d] = v; sig[n-d] = (n - v) % n
        Tp = build_T(p, n, X, (a0*sig) % n)
        Cs.append(abs(np.sum(chi_full[1:]*Tp[1:]**3)))
    pcoh = magC >= np.sqrt(n)*np.median(Cs)

    # ---- B0 ensemble (L2-only, Hermitian): draw magnitudes, record L1 and cubic sum S ----
    L1_list = np.empty(N0); S_list = np.empty(N0, dtype=np.complex128)
    A2b = A2  # (nreps,)
    for i0 in range(0, N0, chunk):
        m = min(chunk, N0-i0)
        xi = rng.standard_exponential((m, nreps))          # Exp(1)
        s2 = E_exact/(2*xi.sum(axis=1))                     # rho_rep^2 = xi * s2
        rho2 = xi * s2[:,None]
        rho = np.sqrt(rho2)
        L1_list[i0:i0+m] = 2*rho.sum(axis=1)               # sum over all b = 2*sum reps
        S_list[i0:i0+m] = (rho**3) @ A2b                    # sum_rep rho^3 (a(b)+a(p-b))
    mean_L1_B0 = L1_list.mean()

    # ---- B ensemble: importance-reweight B0 by Gaussian kernel in (S - C_char) ----
    dS = np.abs(S_list - C_char)
    sig_k = 0.02*magC
    for _ in range(60):                        # widen bandwidth until ESS >= ESS_FLOOR
        w = np.exp(-(dS**2)/(2*sig_k**2))
        sw = w.sum()
        ess = sw*sw/np.sum(w*w) if sw > 0 else 0.0
        if ess >= 300: break
        sig_k *= 1.25
    w = w/ w.sum()
    mean_L1_B = np.sum(w*L1_list)
    var_L1_B = np.sum(w*(L1_list-mean_L1_B)**2)
    sd_L1_B = np.sqrt(var_L1_B)
    z_B = (mean_L1_B - L1_char)/sd_L1_B
    D_slice = (mean_L1_B0 - L1_char)/mean_L1_B0
    Delta_coh = mean_L1_B0 - mean_L1_B
    F_expl = Delta_coh/(mean_L1_B0 - L1_char) if abs(mean_L1_B0-L1_char) > 1e-12 else np.nan

    # ---- CAL-UNDER: a fresh high-weight B0 draw fed as "char" -> z should be ~0 ----
    j = np.argmax(w)                           # a well-coherence-matched B0 sample
    L1_star = L1_list[j]
    z_under = (mean_L1_B - L1_star)/sd_L1_B

    # ---- CAL-OVER: plant a calibrated +1% L1 deficit at fixed E (bisection); reweight B to its S ----
    xi = rng.standard_exponential(nreps); base = np.sqrt(xi*E_exact/(2*xi.sum()))
    med = np.median(base)
    def _mk(kap):
        r = base*np.exp(kap*(base-med)); r *= np.sqrt(E_exact/(2*(r**2).sum())); return r
    targetL1 = 0.99*mean_L1_B0
    lo, hi = 0.0, 6.0
    for _ in range(60):                        # bisection: larger kap -> more spread -> lower L1
        mid = (lo+hi)/2; l1 = 2*_mk(mid).sum()
        if l1 > targetL1: lo = mid
        else: hi = mid
    rho1 = _mk((lo+hi)/2); L1plant = 2*rho1.sum()
    Splant = np.sum(rho1**3 * A2b)
    dS2 = np.abs(S_list - Splant); sk2 = 0.02*abs(Splant) if abs(Splant)>0 else 0.02*magC
    for _ in range(60):
        w2 = np.exp(-(dS2**2)/(2*sk2**2)); s2w = w2.sum()
        ess2 = s2w*s2w/np.sum(w2*w2) if s2w > 0 else 0.0
        if ess2 >= 300: break
        sk2 *= 1.25
    w2n = w2/w2.sum(); m2 = np.sum(w2n*L1_list); v2 = np.sum(w2n*(L1_list-m2)**2)
    z_over = (m2 - L1plant)/np.sqrt(v2)
    plant_def = (m2 - L1plant)/m2

    res = dict(p=p, n=n, pmod4=p%4, E_exact=int(E_exact), E_relerr=abs(E_meas-E_exact)/E_exact,
               absC_over_bound=magC/magbound, u_ok=bool(pdir_u_ok), reC_pos=bool(reC>0),
               pdir=bool(pdir), pcoh=bool(pcoh), L1_char=L1_char, mean_L1_B0=mean_L1_B0,
               mean_L1_B=mean_L1_B, sd_L1_B=sd_L1_B, z_B=z_B, D_slice=D_slice,
               Delta_coh=Delta_coh, F_expl=F_expl, sig_k_over_C=sig_k/magC, ess=ess,
               z_under=z_under, z_over=z_over, plant_def=plant_def,
               cv_char=cv_char, cv_rayleigh=0.5227, maxT_sqp=maxT_sqp)
    if verbose:
        print(f"p={p:6d} m4={p%4} | E_rel={res['E_relerr']:.1e} |C|/bd={res['absC_over_bound']:.3f} "
              f"pdir={int(pdir)} pcoh={int(pcoh)} | D_slice={D_slice:+.4%} z_B={z_B:+.2f} "
              f"Dcoh={Delta_coh:+.3f} Fexpl={F_expl:+.2f} | CALo z={z_over:+.1f}(def{plant_def:+.2%}) "
              f"CALu z={z_under:+.2f} ess={ess:.0f}")
    return res

if __name__ == "__main__":
    seed = 20260817
    primes = SCHEDULE
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        primes = [(151,133),(1249,1303),(2671,2569)]
    t0=time.time(); rows=[]
    for (p, n_exp) in primes:
        r = sp.orbit(p)
        assert r is not None, f"no generator at p={p}"
        n, X, Y, facs = r
        assert n == n_exp, f"n mismatch p={p}: {n} != frozen {n_exp}"
        assert n % 2 == 1, f"n even at p={p}"
        rng = np.random.default_rng(seed + p)
        rows.append(analyze(p, n, X, facs, rng))
    excl = [r['p'] for r in rows if not r['pcoh']]
    kept = [r for r in rows if r['pcoh']]                      # O4: P-COH exclusions, printed
    zs = np.array([r['z_B'] for r in kept]); Z_B = zs.sum()/np.sqrt(len(kept))
    zu = np.array([r['z_under'] for r in kept]); Z_under = zu.sum()/np.sqrt(len(kept))
    D_all = np.array([r['D_slice'] for r in rows])
    print(f"\n=== POOLED (primary over {len(kept)} P-COH-passing primes; excluded {excl}) ===")
    print(f"Z_B (PRIMARY) = {Z_B:+.2f}   [z_B>0 SLICE-BEYOND | ~0 SLICE-DISSOLVE | <-3 O10 super-Rayleigh]")
    print(f"CAL-UNDER pooled = {Z_under:+.2f} (must be in [-3,3])")
    print(f"D_slice: {np.sum(D_all>0)}/{len(rows)} positive; range [{D_all.min():+.3%},{D_all.max():+.3%}]")
    over = [r['z_over'] for r in rows if r['p']>=1249]
    pdef = [r['plant_def'] for r in rows if r['p']>=1249]
    print(f"CAL-OVER (p>=1249): min z_over={min(over):+.1f} (>=+4 req); plant_def range "
          f"[{min(pdef):+.2%},{max(pdef):+.2%}] (~+1% target)")
    print(f"ESS range: [{min(r['ess'] for r in rows):.0f},{max(r['ess'] for r in rows):.0f}]")
    print(f"pdir all pass: {all(r['pdir'] for r in rows)} ; pcoh pass: {sum(r['pcoh'] for r in rows)}/{len(rows)}")
    with open("run_v1_rows.json","w") as f:
        json.dump(rows, f, indent=1, default=float)
    print(f"wall={time.time()-t0:.1f}s ; rows -> run_v1_rows.json")
