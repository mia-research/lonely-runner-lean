#!/usr/bin/env python3
"""
harmonic_deficit_locus_v2.py -- FROZEN runner for PREREG_harmonic_deficit_locus_v1.md.
Tests whether the sub-Rayleigh deficit D(b,c)=|U_char|-E_r|U_rand| concentrates on a
publicly-computable LOCUS in the a0=1 frequency slice, with an out-of-sample replication gate.
NO ECDLP/extraction/secp verdict. Model primes only.

Statistic per categorical partition = between-class SS of <D>_s (one-way dispersion), ranked
against a locus-permutation null (shuffle D over harmonics). P7 = beta-orbit invariance of D.
Gate: LOCUS iff extreme on discovery (perm-p<0.01, majority) AND replicates (perm-p<0.05, majority).
Controls C0..C4 must fire. FLOAT only in |U|/FFT; decisions are integer-rank permutation p-values.
"""
import inspect
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords

R = 200          # random targets for the Rayleigh mean
K = 1000         # locus-permutation draws
SEED = 20260721
DISCOVERY = [163, 211, 349]
REPLICATION = [433, 577, 991, 2089]
EXTENSION = [4099]                 # report-only, not gated

def order3(mod):
    g = 2
    while pow(g, (mod - 1) // 3, mod) == 1:
        g += 1
    return pow(g, (mod - 1) // 3, mod)

def build_U(xi, yi, phase, p):
    H = np.zeros((p, p), dtype=complex)
    np.add.at(H, (xi, yi), phase)
    return np.fft.fft2(H)

# ---- partitions: signature (b,c,p) ONLY (tautology guard). b,c are the meshgrid arrays. ----
def _cube_lut(p):
    e = (p - 1) // 3
    lut = np.array([pow(int(v), e, p) for v in range(p)], dtype=np.int64)
    uniq = sorted(set(int(lut[v]) for v in range(1, p)))
    remap = {v: i for i, v in enumerate(uniq)}
    lab = np.array([remap.get(int(lut[v]), -1) for v in range(p)], dtype=np.int64); lab[0] = -1
    return lab
def P1_chi3b(b, c, p): return _cube_lut(p)[b]
def P2_chi3c(b, c, p): return _cube_lut(p)[c]
def _leg_lut(p):
    lab = np.array([1 if pow(int(v), (p - 1) // 2, p) == 1 else 0 for v in range(p)], dtype=np.int64)
    lab[0] = -1; return lab
def P3_legb(b, c, p): return _leg_lut(p)[b]
def P4_legc(b, c, p): return _leg_lut(p)[c]
def P5_bband(b, c, p):
    lab = (b.astype(np.int64) * 10) // p           # deciles of b
    lab = np.where(b == 0, -1, lab); return lab
def P6_baxis(b, c, p): return np.where(b == 0, 1, 0)
def P6_caxis(b, c, p): return np.where(c == 0, 1, 0)

CATEGORICAL = [("P1_chi3b", P1_chi3b), ("P2_chi3c", P2_chi3c), ("P3_legb", P3_legb),
               ("P4_legc", P4_legc), ("P5_bband", P5_bband), ("P6_baxis", P6_baxis),
               ("P6_caxis", P6_caxis)]

def assert_guard():
    for name, fn in CATEGORICAL:
        args = set(inspect.signature(fn).parameters)
        assert args <= {"b", "c", "p"}, f"TAUTOLOGY GUARD FAIL: {name} reads {args}"

def between_ss_p(D, lab, nz, K, rng):
    """between-class SS of <D>_s vs locus-permutation null. Excludes lab<0 and (0,0)."""
    m = nz & (lab >= 0)
    d = D[m]; l = lab[m].astype(np.int64)
    C = int(l.max()) + 1
    cnt = np.bincount(l, minlength=C).astype(float)
    def T(dv):
        s = np.bincount(l, weights=dv, minlength=C)
        return float(np.sum(cnt * (s / np.maximum(cnt, 1) - dv.mean()) ** 2))
    Tobs = T(d)
    ge = sum(T(rng.permutation(d)) >= Tobs for _ in range(K))
    return Tobs, (ge + 1) / (K + 1)

def beta_orbit_p(D, p, beta, K, rng):
    """P7: is D beta-orbit invariant? W = mean_(b!=0) (D(b,c)-D(beta b,c))^2, two-sided perm-p."""
    Dsh = D[(beta * np.arange(p)) % p, :]
    m = np.ones(D.shape, bool); m[0, :] = False
    diff2 = (D - Dsh) ** 2
    Wobs = float(diff2[m].mean())
    vals = D[m]
    ge = 0
    for _ in range(K):
        sh = rng.permutation(vals)
        Dp = D.copy(); Dp[m] = sh
        ge += (float(((Dp - Dp[(beta * np.arange(p)) % p, :]) ** 2)[m].mean()) <= Wobs)
    return Wobs, (ge + 1) / (K + 1)     # LOW W (<=) => beta-invariant locus

def compute_D(p, n, G, rng):
    xs, ys = group_coords(G, p, n, 0)
    xi = np.array(xs[1:], dtype=np.int64) % p; yi = np.array(ys[1:], dtype=np.int64) % p
    d = np.arange(1, n)
    aUc = np.abs(build_U(xi, yi, np.exp(2j * np.pi * d / n), p))
    acc = np.zeros((p, p))
    for _ in range(R):
        acc += np.abs(build_U(xi, yi, np.exp(2j * np.pi * rng.random(n - 1)), p))
    Er = acc / R
    D = aUc - Er
    # C1 equivariance: (lam,beta) from data
    lam = order3(n); xf = np.array(xs, dtype=np.int64)
    beta = (int(xf[lam % n]) * pow(int(xf[1]), p - 2, p)) % p
    lam_inv = pow(lam, -1, n)
    U2 = np.abs(build_U(xi, yi, np.exp(2j * np.pi * lam_inv * d / n), p))
    c1 = float(np.max(np.abs(aUc[(beta * np.arange(p)) % p, :] - U2)))
    return D, aUc, Er, beta, xi, yi, c1

def run_prime(p, n, G, rng, tag=""):
    D, aUc, Er, beta, xi, yi, c1 = compute_D(p, n, G, rng)
    BB, CC = np.meshgrid(np.arange(p), np.arange(p), indexing='ij')
    nz = ~((BB == 0) & (CC == 0))
    agg = (aUc[nz].mean() - Er[nz].mean()) / Er[nz].mean()
    out = {"p": p, "n": n, "C0_deficit%": 100 * agg, "C1_equiv": c1, "parts": {}}
    for name, fn in CATEGORICAL:
        lab = fn(BB, CC, p)
        T, pv = between_ss_p(D, lab, nz, K, rng)
        out["parts"][name] = pv
    W, pw = beta_orbit_p(D, p, beta, K, rng)
    out["parts"]["P7_betaorbit"] = pw
    # store objects for controls
    out["_D"] = D; out["_nz"] = nz; out["_BB"] = BB; out["_lab_chi3b"] = P1_chi3b(BB, CC, p)
    print(f"  {tag}p={p:5d} n={n:5d}  C0_deficit={out['C0_deficit%']:+.3f}%  C1_equiv={c1:.1e}  "
          + "  ".join(f"{k.split('_')[0]}:{v:.4f}" for k, v in out["parts"].items()), flush=True)
    return out

def gate(name, disc, repl):
    ext = lambda rows: sum(r["parts"][name] < 0.01 for r in rows)
    rep = lambda rows: sum(r["parts"][name] < 0.05 for r in rows)
    is_disc = ext(disc) >= 2                       # majority of 3
    is_repl = rep(repl) >= 3                        # majority of 4
    return is_disc, is_repl

def main():
    assert_guard()
    rng = np.random.default_rng(SEED)
    curves = {}
    for p0 in DISCOVERY + REPLICATION + EXTENSION:
        r = prime_order_curve(p0, p0 + 40)
        if r: curves[r[0]] = r
    print(f"resolved primes: {sorted(curves)}", flush=True)
    print("=== per-prime perm-p per partition (C0 deficit sign, C1 equiv must be ~0) ===", flush=True)
    disc = [run_prime(*curves[p], rng, tag="[D] ") for p in sorted(curves) if p <= max(DISCOVERY)]
    repl = [run_prime(*curves[p], rng, tag="[R] ") for p in sorted(curves) if max(DISCOVERY) < p <= max(REPLICATION)]
    ext  = [run_prime(*curves[p], rng, tag="[E] ") for p in sorted(curves) if p > max(REPLICATION)]

    print("\n=== CONTROLS ===", flush=True)
    print(f"  C0 deficit sign <0 all primes: {all(r['C0_deficit%']<0 for r in disc+repl)}", flush=True)
    print(f"  C1 equivariance <1e-6 all primes: {all(r['C1_equiv']<1e-6 for r in disc+repl)}", flush=True)
    # C2 PLANT (all primes): inject -0.5 into chi3b class 0; P1 must be extreme everywhere
    plant_ps = []
    for r in disc + repl:
        Dp = r["_D"].copy(); Dp[r["_lab_chi3b"] == 0] -= 0.5
        _, pv = between_ss_p(Dp, r["_lab_chi3b"], r["_nz"], 200, rng)
        plant_ps.append(pv)
    print(f"  C2 PLANT (inject into chi3=0, all primes) P1 perm-p: max={max(plant_ps):.4f}  (must be <0.01) -> gate would flag LOCUS: {max(plant_ps)<0.01}", flush=True)
    # C4 floor: held-out random target deficit at smallest prime
    p0 = disc[0]["p"]; n0 = disc[0]["n"]; G0 = curves[p0][2]
    xs, ys = group_coords(G0, p0, n0, 0)
    xi = np.array(xs[1:]) % p0; yi = np.array(ys[1:]) % p0
    aU0 = np.abs(build_U(xi, yi, np.exp(2j*np.pi*rng.random(n0-1)), p0))
    acc = np.zeros((p0,p0))
    for _ in range(R): acc += np.abs(build_U(xi, yi, np.exp(2j*np.pi*rng.random(n0-1)), p0))
    Dfl = aU0 - acc/R
    BB, CC = np.meshgrid(np.arange(p0), np.arange(p0), indexing='ij'); nz0 = ~((BB==0)&(CC==0))
    _, pfl = between_ss_p(Dfl, P1_chi3b(BB,CC,p0), nz0, 400, rng)
    print(f"  C4 FLOOR (random target deficit) P1 perm-p at p={p0}: {pfl:.4f}  (should be in-band, >0.05 typical)", flush=True)

    print("\n=== GATE (per partition: extreme-on-discovery AND replicates) ===", flush=True)
    for name, _ in CATEGORICAL + [("P7_betaorbit", None)]:
        is_d, is_r = gate(name, disc, repl)
        verdict = "LOCUS" if (is_d and is_r) else ("chance(disc-only)" if is_d else "uniform")
        dps = [f"{r['parts'][name]:.3f}" for r in disc]; rps = [f"{r['parts'][name]:.3f}" for r in repl]
        print(f"  {name:14s} disc={dps} repl={rps}  -> {verdict}", flush=True)
    print("\n[done]", flush=True)

if __name__ == "__main__":
    main()
