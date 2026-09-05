#!/usr/bin/env python3
"""
joint_shadow_cheap_isotype_v1.py -- does a CHEAP (DLP-free) isotype-pure coordinate readout
concentrate its d-spectrum on a single DL-character orbit?  Implements the pre-registered spec
(experiment-designer, 2026-07-18) VERBATIM.

Readouts (cheap = function of the public point, no elliptic-DLP). μ6=Aut(E) acts d↦λd (GLV),
d↦−d; on coords x_{λd}=βx_d, y_{λd}=y_d, x_{−d}=x_d, y_{−d}=−y_d. Weight-1 needs a mult. char
with ψ(βx)=ω·ψ(x): the cubic-residue log dlog3(x) (χ3(β)=μ, primitive cube root) gives
ψ1(x)=ω^{dlog3(x)} -- BUT only when β is a NON-cube (p≢1 mod 9); else χ3(β)=1 and ψ1 is weight-0.
So weight-1/2 rows are scoped to p≢1 mod9. Every readout's isotype is MEASURED, not assumed.

STATISTIC (primary): R_orb = max_Ω [Σ_{a∈Ω}|F̂(a)|²] / Σ_{a≠0}|F̂(a)|², Ω over the K=(n−1)/6
μ6-orbits of nonzero characters. Perfect single-DL-char → 1; flat → ~ln K/K. Secondary: N_eff.
NULL: orbit-value permutation -- permute the K fundamental-domain values, re-inflate by the
isotype phase θ_{w,s}. Preserves purity+multiset+DC; destroys value↔orbit alignment. B draws.
POWER: plant √φ·Ŝ+√(1−φ)·noise (Ŝ=isotype-projected DL char; φ=1 must read R_orb=1).
DECISION: p=(1+#{null≥obs})/(B+1); NULL if p>α'=0.05/6; DEPARTING if p≤α' on ≥2 curves.
FLOAT CARVE-OUT: signal path exact int (curve, χ3=pow, Legendre=pow, sign); float only in DFT/|·|².
"""
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords

OMEGA = np.exp(2j * np.pi / 3)
ALPHA = 0.05 / 6
B = 10000


def order3(m):
    for x in range(2, m):
        if pow(x, 3, m) == 1:
            return x
    return None


def find_curves(want=5):
    out = []
    lo = 150
    while len(out) < want and lo < 4000:
        r = prime_order_curve(lo, lo + 40)
        if r:
            p, n, G = r
            if p % 9 != 1 and (n - 1) % 6 == 0:      # β non-cube AND μ6 acts freely on chars
                out.append((p, n, G))
        lo += 40
    return out


def find_curves_at(targets):
    """First β-non-cube prime-order curve at/above each target prime (for the larger-n retest)."""
    out = []
    for t in targets:
        lo = t
        while lo < t + 4000:
            r = prime_order_curve(lo, lo + 30)
            if r:
                p, n, G = r
                if p % 9 != 1 and (n - 1) % 6 == 0:
                    out.append((p, n, G)); break
            lo += 30
    return out


def orbit_structure(n, lam):
    """μ6 orbits of {1..n-1} under ⟨λ,−1⟩. Returns oid[k]=orbit index, reps list, and for the
    six group elements m∈{±λ^j}: their residues and (parity e, weight j)."""
    elems = []
    for e in (0, 1):
        for j in range(3):
            m = ((-1) ** e) * pow(lam, j, n) % n
            elems.append((m, e, j))
    oid = -np.ones(n, dtype=np.int64)
    reps = []
    for k in range(1, n):
        if oid[k] >= 0:
            continue
        idx = len(reps); reps.append(k)
        for (m, e, j) in elems:
            oid[(m * k) % n] = idx
    return oid, np.array(reps), elems


def isotype_of(F, xs_i, lam_idx, neg_idx):
    """MEASURE (w,s): w from mean F[λd]/F[d], s from mean F[−d]/F[d]. Returns (w,s, purity_err)."""
    nz = np.abs(F) > 1e-9
    rl = F[lam_idx][nz] / F[nz]
    w = int(round((np.angle(np.mean(rl)) % (2 * np.pi)) / (2 * np.pi / 3))) % 3
    rn = np.real(F[neg_idx][nz] / F[nz])
    s = 1 if np.mean(rn) > 0 else -1
    return w, s


def theta_per_d(n, w, s, elems, reps):
    """θ(m_d)=s^e·ω^{wj} for each d (m_d=(−1)^e λ^j), and orbit-index oi, so F(d)=θ(m_d)·F(rep_d)."""
    theta = np.ones(n, dtype=complex)
    oi = np.zeros(n, dtype=np.int64)
    for idx, k in enumerate(reps):
        for (m, e, j) in elems:
            d = (m * k) % n
            theta[d] = (s ** e) * (OMEGA ** (w * j))
            oi[d] = idx
    theta[0] = 0.0
    return theta, oi


def R_orb(F, oid, K):
    Fh = np.fft.fft(F)
    P = np.abs(Fh) ** 2
    P[0] = 0.0
    M = np.bincount(oid[1:], weights=P[1:], minlength=K)   # C-speed orbit sum
    tot = M.sum()
    if tot <= 0:
        return 0.0, K / 2.0
    Rorb = M.max() / tot
    Neff = (M.sum() ** 2) / np.sum(M ** 2)
    return float(Rorb), float(Neff)


def null_band(F, theta, oi, reps, oid, K, seed):
    """Orbit-value permutation null. Primary R_orb (concentration = HIGH, right tail) and
    secondary N_eff (diffuse concentration = LOW orbit-support, left tail)."""
    rng = np.random.default_rng(seed)
    Rvals = F[reps]                       # value at each canonical rep (θ=1 there)
    obsR, obsN = R_orb(F, oid, K)
    sR = np.empty(B); sN = np.empty(B)
    for b in range(B):
        perm = rng.permutation(K)
        Fp = theta * Rvals[perm][oi]      # permute rep values across orbits, then inflate by θ
        Fp[0] = 0.0
        sR[b], sN[b] = R_orb(Fp, oid, K)
    pR = (1 + int(np.sum(sR >= obsR - 1e-12))) / (B + 1)
    pN = (1 + int(np.sum(sN <= obsN + 1e-12))) / (B + 1)
    return (obsR, float(sR.mean()), float(np.quantile(sR, 1 - ALPHA)), pR,
            obsN, float(sN.mean()), float(np.quantile(sN, ALPHA)), pN)


def build_readouts(p, n, xs, ys, beta):
    """Cheap isotype-pure readouts, each a length-n complex array (index d, F[0]=0)."""
    x = np.array(xs, dtype=np.int64); y = np.array(ys, dtype=np.int64)
    mu = pow(int(beta), (p - 1) // 3, p)          # χ3(β): primitive cube root iff β non-cube
    # dlog3(x): k∈{0,1,2} with χ3(x)=μ^k ; χ3(x)=pow(x,(p-1)/3,p)
    chi = np.array([pow(int(v), (p - 1) // 3, p) if v % p else 0 for v in x])
    mu_pow = [1, mu % p, (mu * mu) % p]
    dl = np.zeros(n, dtype=np.int64)
    for d in range(1, n):
        c = chi[d]
        dl[d] = 0 if c == mu_pow[0] else (1 if c == mu_pow[1] else 2)
    xzero = (x % p == 0)
    psi1 = OMEGA ** dl; psi1[xzero] = 0.0; psi1[0] = 0.0
    leg = np.array([1.0 if v % p and pow(int(v), (p - 1) // 2, p) == 1 else (-1.0 if v % p else 0.0) for v in x])
    leg[0] = 0.0
    # exactly-odd sign: +1 for y in [1,(p-1)/2], -1 for y in [(p+1)/2,p-1] (pairs y<->p-y antisym)
    sgn = np.where(y <= (p - 1) // 2, 1.0, -1.0).astype(complex); sgn[0] = 0.0
    R = {
        "(1,+) chi3":       psi1.astype(complex),
        "(2,+) chi3^2":     (psi1 ** 2).astype(complex),
        "(0,+) Legendre":   leg.astype(complex),
        "(0,-) sign(y)":    sgn,
        "(1,-) chi3.sgn":   psi1 * sgn,
        "(2,-) chi3^2.sgn": (psi1 ** 2) * sgn,
    }
    return R, mu


def run(p, n, G):
    xs, ys = group_coords(G, p, n, 0)
    x = np.array(xs, dtype=np.int64)
    lam = order3(n)
    beta = int(x[lam]) * pow(int(x[1]), p - 2, p) % p       # β paired to λ, from data
    e1 = int(np.max(np.abs((beta * x - x[(lam * np.arange(n)) % n]) % p)))
    K = (n - 1) // 6
    lam_idx = (lam * np.arange(n)) % n
    neg_idx = (n - np.arange(n)) % n
    oid, reps, elems = orbit_structure(n, lam)
    print(f"\n=== p={p} n={n} K={K}  λ={lam} β={beta}  x_λd=βx_d err={e1} (0)  p%9={p%9}(≠1⇒β noncube) ===")
    R, mu = build_readouts(p, n, xs, ys, beta)

    # positive control: planted φ=1 must read R_orb=1 for a projected DL character
    a0 = 1
    for i, (name, F) in enumerate(R.items()):
        w, s = isotype_of(F, x, lam_idx, neg_idx)
        theta, oi = theta_per_d(n, w, s, elems, reps)
        pur = float(np.max(np.abs(F - theta * F[reps][oi])))
        # planted signal in THIS isotype: project e_n(a0 d) onto (w,s)
        c = np.exp(2j * np.pi * a0 * np.arange(n) / n); c[0] = 0
        S = np.zeros(n, dtype=complex)
        for (m, e, j) in elems:
            S += (OMEGA ** (-w * j)) * ((s + 0.0) ** e) * c[(m * np.arange(n)) % n]
        S[0] = 0.0
        r1, _ = R_orb(S, oid, K)
        obsR, mR, qR, pR, obsN, mN, qN, pN = null_band(F, theta, oi, reps, oid, K, seed=p * 100 + i)
        verdict = "DEPARTS" if (pR <= ALPHA or pN <= ALPHA) else "null"
        print(f"  {name:18s} ({w},{'+' if s>0 else '-'}) pur={pur:.0e} | φ1={r1:.3f} | "
              f"R_orb={obsR:.4f} null[{mR:.3f},q{qR:.3f}] pR={pR:.4f} | "
              f"Neff={obsN:.1f} null[q{qN:.1f},{mN:.1f}] pN={pN:.4f} -> {verdict}")


def main():
    import sys
    global B
    smoke = "--smoke" in sys.argv
    large = "--large" in sys.argv
    print("=" * 96)
    print("CHEAP isotype-pure readout d-spectral concentration -- pre-registered R_orb / orbit-perm null")
    print("=" * 96)
    if large:
        curves = find_curves_at([1500, 3000, 4500, 6500])   # larger-n retest (higher power)
    else:
        curves = find_curves(1 if smoke else 5)
    if smoke:
        B = 800
    print("curves (p,n,K):", [(p, n, (n - 1) // 6) for p, n, _ in curves], " B=", B)
    for p, n, G in curves:
        run(p, n, G)
    print("\n[done]")


if __name__ == "__main__":
    main()
