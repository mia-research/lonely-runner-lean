#!/usr/bin/env python3
"""
harmonic_deficit_locus_v1.py  --  EXPLORATORY QUICK CHECK (NOT a pre-registered test).

Follows RESULT_harmonic_support_pattern_v1.md sec.5: the one live item is a 0.06-0.10% sub-Rayleigh
deficit in mean|U|, one-directional at 7/7 primes, growing to -13.9 sigma at p=2089. This is a SCOPING
look at whether that deficit has any LOCUS / CM-sector structure -- to decide if a full prereg is warranted.
Any number here is EXPLORATORY and may NOT be reported as a confirmed finding; the frozen test comes after.

OBJECT   E: y^2=x^3+7 over F_p, prime order n, a0=1.  U(a0,b,c)=sum_d e_n(a0 d) e_p(b x_d + c y_d).
         D(b,c) = |U_char(b,c)| - E_r|U_rand(b,c)|,  E_r over R random unit-phase targets g(d).
QUESTION (i) reproduce the aggregate deficit  sum_bc D < 0  (sanity vs the RESULT).
         (ii) does D concentrate in specific chi3(b) / CM sectors (or c=0), vs uniform?
STAT     per-sector mean <D>_s for chi3(b) in {0,1,2} and for c==0 vs c!=0.
NULL     locus-permutation: shuffle D across the (b,c) harmonics (preserves the D multiset, destroys
         locus), K times; rank the observed |<D>_s| against the null.  Integer-rank p-value (no float thr).
CONTROLS reproduce deficit sign; C2 equivariance (forced, |U(1,beta b,c)|==|U(lam^-1,b,c)|);
         PLANT: inject a deficit into sector 0 -> the null must flag it.
FLOAT    curve/group + (b,c) grid exact int; float only in |U|/FFT.  Decisions are permutation ranks.
SCOPE    model primes only; NOTHING transfers to secp (2^256).  No ECDLP/extraction/security claim.
"""
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords

R = 200          # random targets for the Rayleigh mean
K = 400          # locus-permutation draws
SEED = 20260721

def order3(mod):
    g = 2
    while pow(g, (mod - 1) // 3, mod) == 1:
        g += 1
    return pow(g, (mod - 1) // 3, mod)

def build_U_from_phase(xi, yi, phase, p):
    H = np.zeros((p, p), dtype=complex)
    np.add.at(H, (xi, yi), phase)
    return np.fft.fft2(H)

def cubic_classes(p):
    e = (p - 1) // 3
    vals = np.array([pow(int(b), e, p) for b in range(p)], dtype=np.int64)
    uniq = sorted(set(int(vals[b]) for b in range(1, p)))
    remap = {v: i for i, v in enumerate(uniq)}
    cls = np.array([remap.get(int(v), -1) for v in vals], dtype=np.int64)
    cls[0] = -1
    return cls

def sector_means(D, clsB, nz, ceq0):
    out = {}
    for s in (0, 1, 2):
        m = nz & (clsB == s)
        out[f"chi3={s}"] = (float(D[m].mean()), int(m.sum()))
    out["c=0"] = (float(D[nz & ceq0].mean()), int((nz & ceq0).sum()))
    return out

def perm_null(D, clsB, nz, ceq0, rng):
    """rank |observed <D>_s| against K shuffles of D over the nz harmonics."""
    vals = D[nz].copy()
    obs = sector_means(D, clsB, nz, ceq0)
    # build masks in nz-space (keys MUST match obs)
    idx_c = {f"chi3={s}": (clsB[nz] == s) for s in (0, 1, 2)}
    idx_c["c=0"] = ceq0[nz]
    ge = {k: 0 for k in obs}
    for _ in range(K):
        sh = rng.permutation(vals)
        for k, mask in idx_c.items():
            nm = sh[mask].mean()
            if abs(nm) >= abs(obs[k][0]):
                ge[k] += 1
    return {k: (obs[k][0], obs[k][1], (ge[k] + 1) / (K + 1)) for k in obs}

def run(p, n, G):
    rng = np.random.default_rng(SEED)
    xs, ys = group_coords(G, p, n, 0)
    xi = np.array(xs[1:], dtype=np.int64) % p
    yi = np.array(ys[1:], dtype=np.int64) % p
    d = np.arange(1, n)

    Uc = build_U_from_phase(xi, yi, np.exp(2j * np.pi * d / n), p)   # a0=1 character
    aUc = np.abs(Uc)
    acc = np.zeros((p, p))
    for _ in range(R):
        ph = np.exp(2j * np.pi * rng.random(n - 1))
        acc += np.abs(build_U_from_phase(xi, yi, ph, p))
    Er = acc / R                                                     # E_r |U_rand(b,c)|
    D = aUc - Er

    BB, CC = np.meshgrid(np.arange(p), np.arange(p), indexing='ij')
    nz = ~((BB == 0) & (CC == 0))
    ceq0 = (CC == 0)
    clsB = cubic_classes(p)[BB]

    print(f"\n=== p={p} n={n}  R={R} K={K} ===")
    # (i) aggregate deficit sanity
    mean_char = aUc[nz].mean(); mean_rand = Er[nz].mean()
    print(f"  aggregate: mean|U_char|={mean_char:.5f}  E_r mean|U|={mean_rand:.5f}  "
          f"deficit={100*(mean_char-mean_rand)/mean_rand:+.3f}%  (RESULT: -0.06..-0.10%)")

    # C2 equivariance (forced). Derive the (lam,beta) PAIR from data: x_{lam d}=beta x_d, y_{lam d}=y_d.
    lam = order3(n)
    xfull = np.array(xs, dtype=np.int64)
    beta = (int(xfull[lam % n]) * pow(int(xfull[1]), p - 2, p)) % p
    ident = int(np.max((beta * xfull[1:] - xfull[(lam * np.arange(1, n)) % n]) % p))
    lam_inv = pow(lam, -1, n)
    U2 = np.abs(build_U_from_phase(xi, yi, np.exp(2j * np.pi * lam_inv * d / n), p))
    eqerr = np.max(np.abs(aUc[(beta * np.arange(p)) % p, :] - U2))
    print(f"  C2 equivariance (forced): lam={lam} beta={beta}  x_lamd=beta*x_d err={ident}  "
          f"|U| shift err={eqerr:.2e}  {'OK' if eqerr < 1e-6 and ident == 0 else 'CHECK'}")

    # (ii) per-sector deficit vs locus-permutation null
    res = perm_null(D, clsB, nz, ceq0, rng)
    print("  SECTOR mean deficit <D>_s  (perm-null p, K draws):")
    for k, (val, cnt, pv) in res.items():
        print(f"     {k:8s}: <D>={val:+.5f}  |sec|={cnt:7d}  perm-p={pv:.4f}")

    # PLANT control: inject a deficit into sector 0, must be flagged
    Dp = D.copy(); Dp[nz & (clsB == 0)] -= 0.5
    resp = perm_null(Dp, clsB, nz, ceq0, rng)
    print(f"  PLANT (inject -0.5 into chi3=0): perm-p chi3=0 -> {resp['chi3=0'][2]:.4f}  (must be small)")

def main():
    for lo, hi in [(160, 200), (340, 360), (570, 590)]:
        r = prime_order_curve(lo, hi)
        if r:
            run(*r)

if __name__ == "__main__":
    main()
