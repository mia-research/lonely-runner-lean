#!/usr/bin/env python3
"""
angular_interference_scaling_v1.py

Operationalizes the "indirect / interference shadow" hypothesis:
  the public point looks random, but a curve-native ANGLE (the CM / mu_6 sextic
  phase of the coordinates) might hold a coherent shadow of the scalar d that only
  shows up when you ACCUMULATE across many keys.

Two decisive, exact tests per angle functional theta(X,Y):

  ARM A -- COHERENCE / interference.  Sum the phases as EXACT Eisenstein integers:
     S = sum_i  u(theta_i),   u : mu_k -> units of Z[omega]  (a fixed injection)
     norm N(S) = a^2 - a*b + b^2   (exact integer, no float).
   Fit log N(S) vs log M over growing M:
     slope ~ 1  => incoherent (random-walk; NO accumulating shadow)
     slope ~ 2  => coherent   (a real phase peak -- an interference pattern)
   A coherent resultant that is IDENTICAL on generated-uniform-d and on the real
   keys is CURVE-FIXED CM geometry, NOT key recovery.  Only a d-correlation
   (Arm B) or a real-vs-generated difference is a key/selection signal.

  ARM B -- CONDITIONAL d-leak (the recovery question).  Bias-corrected MI and
   permutation-z between theta and targets of d (d mod {2,3,5,6,7}, mid/top bits),
   using the power_scaling classifier:
     I_c plateau (loglog slope ~0) AND z ~ sqrt(M)  => SIGNAL (a decodable shadow)
     I_c ~ 1/M  (loglog slope ~ -1) AND z flat      => NOISE

Sets:
  gen256 -- generated keys, d uniform in [2^255,2^256): NON-degenerate GLV, the
            regime the 100k (<=160-bit) never reached; d known -> Arm B computable.
  gen130 -- generated 130-bit (matches the real puzzle frontier) for a degeneracy check.
  real82 -- the actual solved puzzle keys (creator's selection).
  d100k  -- the constructed 100k set (known-MT through the same pipeline).

Exact arithmetic in the signal path (CLAUDE.md).  The only float is inside mi_bits
(a monotone statistic ranked vs a matched permutation null) -- lines carry noqa: float.
"""
import argparse, os, numpy as np
from ecc_secp256k1 import scalar_mul, P as PF, N_ORDER
from reset_common import load_solved

# ---- exact mu_6 / mu_3 / mu_2 characters of a field element -----------------
e6 = (PF - 1) // 6; e3 = (PF - 1) // 3; e2 = (PF - 1) // 2
def _prim6():
    for g in range(2, 200):
        z = pow(g, e6, PF)
        if pow(z, 6, PF) == 1 and all(pow(z, t, PF) != 1 for t in (1, 2, 3)):
            return z
Z6 = _prim6()
SIX = {pow(Z6, j, PF): j for j in range(6)}
Z3 = pow(Z6, 2, PF); THREE = {pow(Z3, j, PF): j for j in range(3)}
def chi6(x): return SIX.get(pow(x % PF, e6, PF))          # 0..5 (None iff x==0)
def chi3(x): return THREE.get(pow(x % PF, e3, PF))        # 0..2
def chi2(x):                                              # 0/1 quadratic char (the "180 deg" sign)
    r = pow(x % PF, e2, PF); return 0 if r == 1 else 1

# ---- Eisenstein-integer units: exact resultant, exact norm ------------------
# omega = primitive cube root, omega^2 = -omega - 1.  Represent a+b*omega as (a,b).
# The 6 sixth-roots of unity = units of Z[omega]:  +-1, +-omega, +-omega^2.
#   omega^2 = -1 - omega  => (-1,-1).
U6 = [(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]   # 1, w, w^2, -1, -w, -w^2 = zeta6^{0..5}
U3 = [(1, 0), (0, 1), (-1, -1)]                              # cube roots
U2 = [(1, 0), (-1, 0)]                                       # +-1
def enorm(a, b): return a * a - a * b + b * b                # N(a+b*omega), exact

def resultant_norm(exps, units):
    a = b = 0
    for e in exps:
        ua, ub = units[e]; a += ua; b += ub
    return enorm(a, b)                                       # exact integer

def coherence(exps, units, M, rng, Breps=200):
    """Coherence of the phase sum at size M.
    ratio = N(S_M)/M : ~1 (chi-square-ish) under a UNIFORM angle marginal (incoherent
    random walk); grows ~M under a coherent shadow (non-zero mean phase).
    Compares to Breps uniform-random baselines of the same alphabet -> exact rank p.
    Returns (obs_norm, ratio, base_ratio_mean, rank_p)."""
    k = len(units)
    obs = resultant_norm(exps[:M], units)
    base = np.array([resultant_norm(rng.integers(0, k, M).tolist(), units)   # noqa: float (baseline)
                     for _ in range(Breps)])
    p = (int(np.sum(base >= obs)) + 1) / (Breps + 1)        # noqa: float (rank p, integer counts)
    return obs, obs / M, float(base.mean()) / M, p          # noqa: float (report ratios)

def loglog_slope(ms, ys):
    x = np.log(np.array(ms, float)); v = np.log(np.abs(np.array(ys, float)) + 1e-9)  # noqa: float
    return float(np.polyfit(x, v, 1)[0])                    # noqa: float

# ---- Arm B: bias-corrected MI + permutation z (power_scaling machinery) ------
def mi_bits(a, b):                                          # noqa: float (ranked statistic)
    nb = int(b.max()) + 1
    joint = np.bincount(a * nb + b, minlength=(int(a.max()) + 1) * nb).reshape(-1, nb)
    n = int(joint.sum()); Pr = joint / n                    # noqa: float
    px = Pr.sum(1, keepdims=True); py = Pr.sum(0, keepdims=True)
    with np.errstate(divide="ignore", invalid="ignore"):
        t = Pr * (np.log2(Pr) - np.log2(px) - np.log2(py))  # noqa: float
    return float(np.nansum(t[Pr > 0]))                      # noqa: float

def conditional(feat, targ, Ms, Bnull, rng):
    out = []
    for M in Ms:
        f = feat[:M]; y = targ[:M]
        raw = mi_bits(f, y)
        nulls = np.array([mi_bits(f, y[rng.permutation(M)]) for _ in range(Bnull)])  # noqa: float
        mu = nulls.mean(); sd = nulls.std() + 1e-12         # noqa: float
        out.append((M, raw - mu, (raw - mu) / sd))          # noqa: float
    return out

# ---- key sets ----------------------------------------------------------------
def gen_keys(bitlen, M, seed):
    """M keys with known d, uniform bit-length `bitlen`, exact point.  Cached."""
    cache = os.path.join(os.path.dirname(__file__), f"_angcache_b{bitlen}_M{M}_s{seed}.npz")
    if os.path.exists(cache):
        z = np.load(cache, allow_pickle=True)
        return list(z["d"]), list(z["X"]), list(z["Y"])
    rng = np.random.default_rng(seed)
    lo = 1 << (bitlen - 1); span = lo
    ds = []; Xs = []; Ys = []
    for i in range(M):
        d = lo + int.from_bytes(rng.bytes((bitlen + 7) // 8), "big") % span
        xy = scalar_mul(d)
        ds.append(d); Xs.append(xy[0]); Ys.append(xy[1])
        if (i + 1) % 5000 == 0: print(f"    gen b{bitlen}: {i+1}/{M}")
    np.savez(cache, d=np.array(ds, dtype=object), X=np.array(Xs, dtype=object),
             Y=np.array(Ys, dtype=object))
    return ds, Xs, Ys

def load_100k():
    import csv
    d = []; X = []; Y = []
    with open(os.path.join(os.path.dirname(__file__), "constructed_keys_1to160_100k_exact.csv")) as f:
        for r in csv.DictReader(f):
            if int(r["bits"]) < 40:  # non-degenerate-ish, matches power_scaling default
                continue
            d.append(int(r["d"])); X.append(int(r["X"], 16)); Y.append(int(r["Y"], 16))
    return d, X, Y

# ---- angle functionals -------------------------------------------------------
def angles(X, Y):
    a6X = [chi6(x) for x in X]
    a6Y = [chi6(y) for y in Y]
    a3X = [chi3(x) for x in X]
    a2Y = [chi2(y) for y in Y]           # the "~180 deg" quadratic phase of Y
    a12 = [6 * chi2(y) + chi6(x) for x, y in zip(X, Y)]  # 12-sector (sign x sextic)
    return {"chi6(X)": (a6X, U6), "chi6(Y)": (a6Y, U6), "chi3(X)": (a3X, U3),
            "chi2(Y)": (a2Y, U2)}, a12

def d_targets(ds):
    tg = {}
    for m in (2, 3, 5, 6, 7):
        tg[f"d%{m}"] = np.array([int(v) % m for v in ds], dtype=np.int64)
    tg["bit_mid"] = np.array([(int(v) >> (int(v).bit_length() // 2)) & 1 for v in ds], dtype=np.int64)
    return tg

def run_set(name, ds, Xs, Ys, Ms, Bnull, do_cond):
    print(f"\n{'='*72}\nSET {name}  (M={len(ds)})\n{'='*72}")
    fam, _ = angles(Xs, Ys)
    rngA = np.random.default_rng(2024)
    print("\n[ARM A] coherence  ratio=N(S)/M   (~1 => uniform/incoherent; grows with M => coherent shadow)")
    print(f"  {'angle':10} {'ratio@Msmall':>13} {'ratio@Mfull':>12} {'base~1':>8} {'rank_p':>8}  verdict")
    Mfull = min(len(fam[list(fam)[0]][0]), max(Ms))
    Msmall = max(1, Mfull // 10)
    for nm, (exps0, units) in fam.items():
        exps = [e for e in exps0 if e is not None]
        Mf = min(Mfull, len(exps)); Ms_ = max(1, Mf // 10)
        _, r_s, _, _ = coherence(exps, units, Ms_, rngA)
        obs, r_f, base_f, p = coherence(exps, units, Mf, rngA)
        grows = r_f > 3 * r_s and r_f > 5      # coherent shadow both large and growing
        verdict = "COHERENT" if (p < 0.01 and grows) else ("nonunif?" if p < 0.01 else "uniform")  # noqa: float (verdict threshold, not a data cut)
        print(f"  {nm:10} {r_s:>13.2f} {r_f:>12.2f} {base_f:>8.2f} {p:>8.4f}  {verdict}")
    if not do_cond:
        print("\n[ARM B] skipped (no known d for this set).")
        return
    print("\n[ARM B] conditional d-leak: bias-corr MI I_c (bits) and permutation z at growing M")
    rng = np.random.default_rng(31337)
    tg = d_targets(ds)
    Mc = [m for m in Ms if m <= len(ds)]
    for nm, (exps, units) in fam.items():
        feat = np.array([e if e is not None else 0 for e in exps], dtype=np.int64)
        best = None
        for tn, tv in tg.items():
            res = conditional(feat, tv, Mc, Bnull, rng)
            Ic = [r[1] for r in res]; z = [r[2] for r in res]
            s_mi = loglog_slope(Mc, Ic)
            s_z = float(np.polyfit(np.sqrt(np.array(Mc, float)), np.array(z, float), 1)[0])  # noqa: float
            verdict = "SIGNAL" if (s_mi > -0.5 and s_z > 0 and z[-1] > 3) else "noise"  # noqa: float (slope classifier, not a data threshold)
            cand = (z[-1], tn, Ic[-1], s_mi, s_z, verdict)
            if best is None or z[-1] > best[0]:
                best = cand
        zL, tn, IcL, s_mi, s_z, verdict = best
        print(f"  {nm:10} strongest target={tn:8} I_c={IcL:+.5f}  z={zL:+.2f}  "
              f"loglogslope={s_mi:+.2f} z/sqrtM={s_z:+.4f}  => {verdict}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=40000)
    ap.add_argument("--Bnull", type=int, default=200)
    ap.add_argument("--sets", default="gen256,gen130,real82,d100k")
    a = ap.parse_args()
    Ms = [500, 1000, 2000, 5000, 10000, 20000, a.M]
    Ms = sorted(set(m for m in Ms if m <= a.M))
    sets = a.sets.split(",")

    if "gen256" in sets:
        d, X, Y = gen_keys(256, a.M, 7)
        run_set("gen256 (uniform d, non-degenerate GLV)", d, X, Y, Ms, a.Bnull, True)
    if "gen130" in sets:
        d, X, Y = gen_keys(130, a.M, 11)
        run_set("gen130 (uniform d, puzzle frontier)", d, X, Y, Ms, a.Bnull, True)
    if "d100k" in sets:
        d, X, Y = load_100k()
        run_set("d100k (known-MT, same pipeline)", d, X, Y, Ms, a.Bnull, True)
    if "real82" in sets:
        s = load_solved()
        keys = [k for k in sorted(s) if s[k]["X"] is not None]
        d = [s[k]["d"] for k in keys]; X = [s[k]["X"] for k in keys]; Y = [s[k]["Y"] for k in keys]
        run_set("real82 (creator selection; low M -> Arm A only, low power)",
                d, X, Y, [len(d)], a.Bnull, False)

if __name__ == "__main__":
    main()
