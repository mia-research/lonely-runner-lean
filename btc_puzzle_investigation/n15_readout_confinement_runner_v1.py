#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
n15_readout_confinement_runner_v1.py

Executes PREREG_n15_joint_readout_confinement_v1.md (SHA printed at run).

Object (N15, well-posed reframing): does the JOINT public readout
  T(d) = ( e([d]G), s-class([d]G), y-parity([d]G) )      (18 cells)
of a single target point carry information about BOUNDED-COMPLEXITY (cheap)
arithmetic functions C(d) of the scalar, beyond the per-readout marginals, on
KNOWN-d secp256k1 keys constructed on demand? A positive => an operational cheap
keyspace pre-filter (compute cheap C(d') for candidates, keep only those whose
predicted T matches T(P), do the scalar-mult only on survivors).

PRIMARY statistic S = Î(C ; T | band b), plug-in MI in bits (Miller-Madow value
also reported), ranked against the within-band C<->T permutation null (B perms,
exact integer count p). Chain-rule secondary terms I(C;e), I(C;s|e), I(C;yp|e,s).
Diagnostics H(d|T,I) (ceiling log2 18) and total correlation TC. Firing control:
epsilon-plant c*(d)=e w.p. eps (must fire at eps=1, monotone). Hard null: FP rate.

EXACT signal path (CLAUDE.md): scalar mult, x/y, e (int modpow), carry_c (int
Babai), y-parity (int compare), C (int mod / int modpow / bit ops). Float appears
ONLY inside the MI log and in reported ratios, always ranked against the exact
integer permutation count -> every such line is tagged  # noqa: float.
"""
import argparse, os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ecc_secp256k1 import scalar_mul, P as PF, N_ORDER

p = PF                      # secp field prime
n = N_ORDER                # secp group order (prime)
assert p == 2**256 - 2**32 - 977
assert n % 3 == 1          # cube character well-defined

# ---- cubic readout e (multiplicative cubic character of x) --------------------
_g = 2
while pow(_g, (p - 1) // 3, p) == 1:
    _g += 1
BETA3 = pow(_g, (p - 1) // 3, p)          # primitive cube root of unity mod p
BETA3_2 = pow(BETA3, 2, p)
def e_of(x):
    t = pow(x, (p - 1) // 3, p)
    return 0 if t == 1 else (1 if t == BETA3 else 2)

# ---- s-class = 3-class Eisenstein carry c(X) {3/4,1/8,1/8} (validated, n16) ----
A_SP = 367917413016453100223835821029139468249
B_SP = 64502973549206556628585045361533709078
BETA_C = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
assert A_SP * A_SP - A_SP * B_SP + B_SP * B_SP == p
def _lift_uv(X):
    ku = (2 * X * (A_SP - B_SP) + p) // (2 * p)
    kv = (-2 * X * B_SP + p) // (2 * p)
    return X * (A_SP - B_SP) - ku * p, -X * B_SP - kv * p
def _z_lift(X):
    u_num, v_num = _lift_uv(X)
    ku = (X * (A_SP - B_SP) - u_num) // p
    kv = (-X * B_SP - v_num) // p
    return X - ku * A_SP + kv * B_SP, -ku * B_SP - kv * (A_SP - B_SP)
def _carry_c(X):
    z0, z1 = _z_lift(X)
    w0, w1 = -z1, z0 - z1                  # omega * z
    r0, r1 = _z_lift(BETA_C * X % p)
    t0, t1 = w0 - r0, w1 - r1
    x_num = (A_SP - B_SP) * t0 + B_SP * t1
    y_num = -B_SP * t0 + A_SP * t1
    assert x_num % p == 0 and y_num % p == 0
    return (x_num // p, y_num // p)
_CARRY_MAP = {(0, 0): 0, (0, 1): 1, (0, -1): 2}
def s_of(x):
    c = _carry_c(x)
    lab = _CARRY_MAP.get(c)
    if lab is None:                        # any further flap value -> class 2
        lab = 2
    return lab

# ---- y-parity ----------------------------------------------------------------
def yp_of(y):
    return 1 if 2 * y >= p else 0

# ---- cheap predictor vector C(d) (frozen, bounded-complexity) -----------------
def C_components(d, b):
    jac = pow(d, (n - 1) // 2, n)          # 1 or n-1
    jacb = 1 if jac == 1 else 0
    cres = pow(d, (n - 1) // 3, n)         # cube char of d mod n (3 values)
    hi3 = (d >> (b - 3)) & 7
    lo3 = d & 7
    return (d % 3, d % 6, d % 7, d % 9, d % 12, jacb, cres, hi3, lo3)

# ================= dataset construction (known-d, on demand) ==================
def build_band(b, N, seed, enumerate_all=False):
    """Return dict of int arrays: e, s, yp, T, and C columns; over N keys in band b
    (or the FULL band 2^(b-1) keys if enumerate_all)."""
    lo = 1 << (b - 1)
    if enumerate_all:
        ds = range(lo, 1 << b)
        N = (1 << b) - lo
    else:
        rng = np.random.default_rng(seed)
        ds = (lo + int.from_bytes(rng.bytes((b + 7) // 8), "big") % lo for _ in range(N))
    e = np.empty(N, np.int8); s = np.empty(N, np.int8); yp = np.empty(N, np.int8)
    cres_raw = np.empty(N, object)
    Ccols = [np.empty(N, np.int64) for _ in range(9)]
    dlow = np.empty(N, np.int64)           # low bits of d, for plant seeding only
    for i, d in enumerate(ds):
        x, y = scalar_mul(d)
        e[i] = e_of(x); s[i] = s_of(x); yp[i] = yp_of(y)
        comp = C_components(d, b)
        for j in range(9):
            Ccols[j][i] = comp[j] if j != 6 else 0
        cres_raw[i] = comp[6]
        dlow[i] = d & ((1 << 40) - 1)
    # rank cube-residue-of-d to a small label (3 values since 3 | n-1)
    _, cres_lab = np.unique(cres_raw.astype(object), return_inverse=True)
    Ccols[6] = cres_lab.astype(np.int64)
    T = (e.astype(np.int64) * 6 + s.astype(np.int64) * 2 + yp.astype(np.int64))
    return dict(N=N, b=b, e=e, s=s, yp=yp, T=T, Ccols=Ccols, dlow=dlow)

def code_of(cols):
    """Rank the tuple of columns to a dense 0..K-1 code over realized support."""
    stacked = np.stack(cols, axis=1)
    _, inv = np.unique(stacked, axis=0, return_inverse=True)
    return inv.astype(np.int64), int(inv.max()) + 1

# ============================ MI machinery ====================================
def mi_bits(code, K, tgt, L):
    """plug-in MI(code;tgt) in bits and Miller-Madow correction (float carve-out)."""
    N = code.shape[0]
    joint = np.bincount(code * L + tgt, minlength=K * L)
    rc = np.bincount(code, minlength=K)
    cc = np.bincount(tgt, minlength=L)
    nz = joint > 0
    jc = joint[nz]
    ci = (np.arange(K * L)[nz] // L)
    ti = (np.arange(K * L)[nz] % L)
    # plug-in MI in bits                                            # noqa: float
    mi = np.sum(jc / N * np.log2(jc * N / (rc[ci] * cc[ti])))       # noqa: float
    mm = mi + (np.count_nonzero(nz) - np.count_nonzero(rc) - np.count_nonzero(cc) + 1) / (2 * N * np.log(2))  # noqa: float
    return float(mi), float(mm)                                     # noqa: float

NAMES = ["d%3", "d%6", "d%7", "d%9", "d%12", "jac", "cres", "hi3", "lo3"]

def build_family(cols):
    """Frozen family F (D1): 9 singletons + 36 pairs, each dense-coded (estimable)."""
    import itertools
    fam = []
    for j, nm in enumerate(NAMES):
        code, K = code_of([cols[j]]); fam.append((nm, code, K))
    for a, b in itertools.combinations(range(9), 2):
        code, K = code_of([cols[a], cols[b]]); fam.append((NAMES[a] + "+" + NAMES[b], code, K))
    return fam

def family_perm(fam, tgt, L, B, seed):
    """max_f I(f;tgt) with family-wise perm p (permute tgt) + per-predictor ge."""
    from fractions import Fraction
    obs = [mi_bits(code, K, tgt, L)[0] for _, code, K in fam]
    obs_max = max(obs); imax = obs.index(obs_max)
    rng = np.random.default_rng(seed); t = tgt.copy()
    ge_s = [0] * len(fam); ge_fam = 0
    for _ in range(B):
        rng.shuffle(t)
        pm = [mi_bits(code, K, t, L)[0] for _, code, K in fam]
        pmax = max(pm)
        for i, m in enumerate(pm):
            if m >= obs[i] - 1e-15:                                # noqa: float
                ge_s[i] += 1
        if pmax >= obs_max - 1e-15:                                # noqa: float
            ge_fam += 1
    return obs, imax, ge_s, Fraction(1 + ge_fam, 1 + B)

# ============================ report per band =================================
def analyze(ds, B, seed, label):
    from fractions import Fraction
    T = ds["T"].astype(np.int64); N = ds["N"]; b = ds["b"]; cols = ds["Ccols"]
    fam = build_family(cols)
    print(f"\n{'='*78}\n[{label}]  band b={b}  N={N}  |family|={len(fam)} (9 singletons + 36 pairs)  |T|=18")
    obs, imax, ge_s, pfam = family_perm(fam, T, 18, B, seed)
    print(f"  PRIMARY  max predictor = {fam[imax][0]}   S_max=I(f;T)={obs[imax]:.4e} bits   "  # noqa: float
          f"family p_perm={float(pfam):.4g}")                                                   # noqa: float
    order = sorted(range(len(fam)), key=lambda i: -obs[i])[:6]
    for i in order:
        ps = Fraction(1 + ge_s[i], 1 + B)
        print(f"    {fam[i][0]:>12}  I(f;T)={obs[i]:.4e}  single p={float(ps):.4g}  (K={fam[i][2]})")  # noqa: float
    # per-readout breakdown for singletons ("beyond individual readouts")
    e = ds["e"].astype(np.int64); s = ds["s"].astype(np.int64); yp = ds["yp"].astype(np.int64)
    print("  per-readout MI for singletons  I(f;e) / I(f;s) / I(f;yp):")
    for j, nm in enumerate(NAMES):
        code, K = code_of([cols[j]])
        ie = mi_bits(code, K, e, 3)[0]; iss = mi_bits(code, K, s, 3)[0]; iy = mi_bits(code, K, yp, 2)[0]
        print(f"    {nm:>6}: {ie:.4e} / {iss:.4e} / {iy:.4e}")                  # noqa: float
    # diagnostics
    def H(arr, L):
        c = np.bincount(arr, minlength=L); c = c[c > 0]
        return float(-np.sum(c / arr.shape[0] * np.log2(c / arr.shape[0])))     # noqa: float
    HT = H(T, 18); He = H(e, 3); Hs = H(s, 3); Hyp = H(yp, 2); TC = He + Hs + Hyp - HT
    mi_min_s = 17 * 11 / (2 * N * np.log(2)); mi_min_p = 17 * 107 / (2 * N * np.log(2))  # noqa: float
    print(f"  diag     H(T)={HT:.4f} (ceil log2 18={np.log2(18):.4f})  H(d|T,I)={(b-1)-HT:.4f}  "  # noqa: float
          f"TC={TC:.4f}   MI_floor singleton~{mi_min_s:.2e} pair~{mi_min_p:.2e}")                  # noqa: float
    return dict(Smax=obs[imax], best=fam[imax][0], pfam=pfam, HT=HT, TC=TC,
                mi_min_s=mi_min_s, mi_min_p=mi_min_p)

# ============================ firing control =================================
def plant_test(ds, B, seed):
    """c*(d)=e w.p. eps else uniform{0,1,2}, tested as a predictor vs T; must fire at eps=1."""
    from fractions import Fraction
    print(f"\n{'-'*78}\n[PLANT eps-ladder]  c* vs T  (VOID unless eps=1 fires p<0.001; want monotone)")
    e = ds["e"].astype(np.int64); T = ds["T"].astype(np.int64); N = ds["N"]
    rng = np.random.default_rng(seed ^ 0xB16B00B5)
    prev = None; mono = True; fired1 = False; mis = {}
    for num in (0, 1, 2, 4, 8, 16, 32, 64):          # eps = num/64
        r = rng.integers(0, 64, size=N); unif = rng.integers(0, 3, size=N)
        cstar = np.where(r < num, e, unif)
        code, K = code_of([cstar])
        mi = mi_bits(code, K, T, 18)[0]
        t = T.copy(); rr = np.random.default_rng(seed + num); ge = 0
        for _ in range(B):
            rr.shuffle(t)
            if mi_bits(code, K, t, 18)[0] >= mi - 1e-15:           # noqa: float
                ge += 1
        pv = Fraction(1 + ge, 1 + B)
        print(f"  eps={num:2d}/64  I(c*;T)={mi:.5e}  p_perm={float(pv):.4g} ({ge}/{B})")  # noqa: float
        mis[num] = mi
        if num == 64:
            fired1 = pv < Fraction(1, 1000)
        # monotone judged only over the above-floor rungs (>= 4/64); sub-floor wiggle ignored
        if num >= 4 and prev is not None and mi + 1e-9 < prev:      # noqa: float
            mono = False
        if num >= 4:
            prev = mi
    print(f"  => eps=1 fires (p<0.001): {fired1};  monotone (eps>=4/64): {mono}  "
          f"[needs B>=1000 for p<0.001; I(c*;T)@eps=1={mis[64]:.4f}~log2 3]")   # noqa: float
    return fired1, mono

# ============================ hard null ======================================
def hard_null(ds, R, B, seed):
    """C paired with random-shuffled T (a genuine null): family FP@alpha over R must be <=2a."""
    from fractions import Fraction
    alpha = Fraction(1, 20)
    print(f"\n{'-'*78}\n[HARD NULL]  {R} random C<->T re-pairings; family FP@{alpha} must be <=2a")
    cols = ds["Ccols"]; T = ds["T"].astype(np.int64); fam = build_family(cols)
    rng = np.random.default_rng(seed ^ 0xDEADBEEF)
    fp = 0
    for _ in range(R):
        Tj = T.copy(); rng.shuffle(Tj)                # genuine null dataset
        _, _, _, pfam = family_perm(fam, Tj, 18, B, int(rng.integers(1 << 30)))
        if pfam < alpha:
            fp += 1
    disp = fp / R                                                              # noqa: float
    print(f"  family FP@{alpha} = {fp}/{R} = {disp:.3f}  (target <= {2*alpha})")  # noqa: float
    return Fraction(fp, R)

# ================================ main =======================================
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bands", type=int, nargs="+", default=[32, 64])
    ap.add_argument("--N", type=int, default=20000)
    ap.add_argument("--B", type=int, default=2000)
    ap.add_argument("--enum", type=int, nargs="*", default=[], help="bands to fully enumerate")
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--plant-band", type=int, default=None, help="band to run plant+hardnull on")
    ap.add_argument("--plant-N", type=int, default=5000, help="N for plant/hardnull (strong effect, small N ok)")
    ap.add_argument("--hardnull-R", type=int, default=40)
    ap.add_argument("--hardnull-B", type=int, default=299)
    a = ap.parse_args()
    import hashlib
    here = os.path.dirname(os.path.abspath(__file__))
    pre = os.path.join(here, "PREREG_n15_joint_readout_confinement_v1.md")
    if os.path.exists(pre):
        print("PREREG SHA-256:", hashlib.sha256(open(pre, "rb").read()).hexdigest())
    print(f"secp p ok; n%3={n%3}; BETA3 set; carry {{3/4,1/8,1/8}} 3-class; T=18 cells")

    results = {}
    for b in a.bands:
        ds = build_band(b, a.N, a.seed + b)
        results[b] = analyze(ds, a.B, a.seed + b, f"sample N={a.N}")
    for b in a.enum:
        ds = build_band(b, 0, a.seed + b, enumerate_all=True)
        results[("enum", b)] = analyze(ds, a.B, a.seed + b, "FULL-ENUM (exact)")

    pband = a.plant_band if a.plant_band is not None else a.bands[0]
    dsp = build_band(pband, a.plant_N, a.seed + pband)
    fired1, mono = plant_test(dsp, a.B, a.seed + pband)
    fpr = hard_null(dsp, a.hardnull_R, a.hardnull_B, a.seed + pband)

    from fractions import Fraction
    fpr_ok = fpr <= Fraction(1, 10)
    print(f"\n{'='*78}\nADMISSIBILITY: eps=1 fired={fired1}  plant-monotone={mono}  "
          f"hardnull FP={float(fpr):.3f}<=0.10={fpr_ok}")                       # noqa: float
    print("If eps=1 did not fire => VOID (instrument dead, no null banked).")

if __name__ == "__main__":
    main()
