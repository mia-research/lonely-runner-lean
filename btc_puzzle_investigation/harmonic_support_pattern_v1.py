#!/usr/bin/env python3
"""
harmonic_support_pattern_v1.py -- executes PREREG_harmonic_support_pattern_v1.md EXACTLY.

OBJECT: the DISTRIBUTION of the individual nonnegative numbers |U(a0,b,c)| across (b,c),
within the conserved budget.  Sector totals (the 1/6 equipartition, the flat CM weights)
cannot see this; the ceiling 4sqrt(p)+1 and the conservation sum_b|T|^2=p(n-2) bracket it
but do not shape it.

ARM A  characterization of the profile (no pass/fail)          -- topk, Neff, max, quantiles
ARM B  does the ACTIVE SET carry d, or is it the geometry's?    -- pattern stat vs R random targets
ARM C  is the active set predictable by a d-FREE selector?      -- AUC / KW vs permutation null

Every threshold that decides anything is a RANK or PERMUTATION statistic (folder float rule);
float appears only in |U| magnitudes / FFT, never on a key or d-secret path.  C1/C2 are 1e-6
readout validations, not evidence.
"""
import inspect
import math
import sys
import numpy as np

from t_y_maxbound_v1 import prime_order_curve, group_coords, legendre
from joint_shadow_decompose_v1 import build_U, glv_beta

EPS = 1e-9
R_NULL = 200
TOPF = (0.01, 0.05, 0.10, 0.25)
PRIMES = [(150, 175), (200, 230), (340, 360), (420, 445), (570, 600), (990, 1100), (1900, 2100)]


# ----------------------------------------------------------------- Arm A descriptors
def profile(mag):
    """Shape descriptors of a nonnegative magnitude array (already flattened, (0,0) removed)."""
    m = np.sort(mag)[::-1]
    tot = m.sum()
    s1 = float(tot)
    s2 = float((m ** 2).sum())
    out = {}
    for f in TOPF:
        k = max(1, int(round(f * m.size)))
        out["top%.2f" % f] = float(m[:k].sum() / tot) if tot > 0 else 0.0
    out["Neff_frac"] = float((s1 * s1 / s2) / m.size) if s2 > 0 else 0.0
    out["q50"] = float(np.quantile(mag, 0.50))
    out["q90"] = float(np.quantile(mag, 0.90))
    out["q99"] = float(np.quantile(mag, 0.99))
    out["max"] = float(m[0])
    return out


def spectrum_of_target(xs, ys, p, g):
    """U_g[b,c] = sum_d g(d) e_p(b x_d + c y_d)  for an arbitrary target g over d=1..n-1."""
    xi = np.array(xs[1:], dtype=np.int64)
    yi = np.array(ys[1:], dtype=np.int64)
    H = np.zeros((p, p), dtype=complex)
    np.add.at(H, (xi, yi), g)
    return np.fft.fft2(H)


def flat_mag(U, p):
    """|U| over S = all (b,c) != (0,0), flattened."""
    m = np.abs(U).ravel().copy()
    m[0] = np.nan                      # (b,c)=(0,0) excluded from S
    return m[~np.isnan(m)]


# ----------------------------------------------------------------- Arm C: d-FREE selectors
# TAUTOLOGY GUARD (prereg section 4): each selector's signature must be a subset of {b,c,p,n}.
# It may NOT read a0, d, xs, ys, U, or any d-indexed array.  Asserted at runtime below.

def s1_legendre(b, c, p, n):
    return np.where(b == 0, 0, np.array([legendre(int(v), p) for v in b]))


def s2_chi3(b, c, p, n):
    """cubic-character class of b in {0,1,2} (b=0 -> -1, excluded)."""
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    w = pow(g, e, p)                                    # primitive cube root of 1 mod p
    lut = {1: 0, w: 1, pow(w, 2, p): 2}
    return np.array([-1 if int(v) == 0 else lut[pow(int(v), e, p)] for v in b])


def s3_small_b(b, c, p, n):
    return ((b >= 1) & (b <= p // 10)).astype(int)


def s4_glv_sector(b, c, p, n):
    """1 iff b is the minimal element of its beta-orbit {b, beta b, beta^2 b}.  d-free."""
    be = glv_beta(p)
    bb = b.astype(np.int64)
    o1 = (bb * be) % p
    o2 = (o1 * be) % p
    return ((bb <= o1) & (bb <= o2) & (bb != 0)).astype(int)


def s5_c_zero(b, c, p, n):
    return (c == 0).astype(int)


def s6_noise(b, c, p, n):
    """C4 negative plant: pure d-free noise of (b,c); must land in the permutation band."""
    return ((b.astype(np.int64) * 2654435761 + c.astype(np.int64) * 40503) % 2).astype(int)


SELECTORS = [("s1_legendre", s1_legendre), ("s2_chi3", s2_chi3),
             ("s3_small_b", s3_small_b), ("s4_glv_sector", s4_glv_sector),
             ("s5_c_zero", s5_c_zero), ("s6_noise[C4 plant]", s6_noise)]
ALLOWED_ARGS = {"b", "c", "p", "n"}


def auc_from_ranks(ranks, lab):
    """AUC for binary lab in {0,1} from precomputed ranks of the target."""
    n1 = int(lab.sum()); n0 = int(lab.size - n1)
    if n1 == 0 or n0 == 0:
        return float("nan")
    return float((ranks[lab == 1].sum() - n1 * (n1 + 1) / 2.0) / (n1 * n0))


def kw_from_ranks(ranks, lab, classes):
    """Kruskal-Wallis H from ranks for a categorical label."""
    N = ranks.size
    H = 0.0
    for cl in classes:
        idx = (lab == cl)
        ni = int(idx.sum())
        if ni == 0:
            continue
        Ri = float(ranks[idx].sum())
        H += Ri * Ri / ni
    return float(12.0 / (N * (N + 1)) * H - 3 * (N + 1))


# ----------------------------------------------------------------- per-prime run
def run_prime(lo, hi, rng):
    r = prime_order_curve(lo, hi)
    if not r:
        return None
    p, n, G = r
    xs, ys = group_coords(G, p, n, 0)
    sp = math.sqrt(p)
    a0 = 1
    print("=" * 112)
    print("p=%d  n=%d  |S|=%d   a0=%d   sqrt(p)=%.3f" % (p, n, p * p - 1, a0, sp))
    print("=" * 112)

    U = build_U(xs, ys, p, n, a0)
    mag = flat_mag(U, p)

    # ---------------- C1 well-posedness: Corr via point space == (1/(n-1)) sum|U|
    Fh = np.zeros_like(U)
    nz = np.abs(U) > EPS
    Fh[nz] = U[nz] / np.abs(U[nz])
    Fh[0, 0] = 0.0
    Fg = np.fft.ifft2(Fh) * (p * p)
    xi = np.array(xs[1:], dtype=np.int64); yi = np.array(ys[1:], dtype=np.int64)
    w1 = np.exp(2j * np.pi * a0 * np.arange(1, n) / n)
    corr_pt = abs(np.mean(Fg[xi, yi] * np.conj(w1)))
    corr_direct = float(np.abs(U)[nz].sum() - (np.abs(U[0, 0]) if nz[0, 0] else 0.0)) / (n - 1)
    rel = abs(corr_pt - corr_direct) / max(corr_direct, 1e-18)
    c1 = rel < 1e-6
    print("  C1 well-posedness  Corr(point-space)=%.6f  Corr=(1/(n-1))sum|U|=%.6f  rel=%.2e  -> %s"
          % (corr_pt, corr_direct, rel, "FIRED" if c1 else "FAIL"))

    # ---------------- C2 equivariance readout: |U(a0,beta b,c)| == |U(lam^-1 a0, b, c)|
    # lambda and beta must be PAIRED by the data (x_{lambda d} = beta x_d): there are two order-3
    # elements mod n and two mod p, and the identity holds only for the matching pair.  Picking
    # them independently breaks C2 at some primes (it did, at p=433,577 -- see DEVIATIONS).
    lam = None
    for t in range(2, n):
        if pow(t, 3, n) == 1 and t != 1:
            lam = t; break
    xa = np.array(xs, dtype=np.int64)
    d_ref = 1
    while d_ref < n and xa[d_ref] == 0:
        d_ref += 1
    be = int((xa[(lam * d_ref) % n] * pow(int(xa[d_ref]), p - 2, p)) % p)   # beta paired to lambda
    pair_err = int(np.max((xa[(lam * np.arange(1, n)) % n] - be * xa[1:]) % p))
    print("  C2 pairing check   lambda=%d -> beta=%d (from data)   max|x_{lam d} - beta x_d| mod p = %d"
          % (lam, be, pair_err))
    laminv = pow(lam, n - 2, n)
    U2 = build_U(xs, ys, p, n, (laminv * a0) % n)
    bidx = (be * np.arange(p)) % p
    c2err = float(np.max(np.abs(np.abs(U[bidx, :]) - np.abs(U2))))
    c2 = c2err < 1e-6
    print("  C2 equivariance    lambda=%d beta=%d   max||U(a0,beta b,c)|-|U(lam^-1 a0,b,c)||=%.2e -> %s"
          % (lam, be, c2err, "FIRED (forced, zero evidence)" if c2 else "FAIL"))

    # ---------------- C5 floor: random-phase U
    gfloor = np.exp(2j * np.pi * rng.random(n - 1))
    magfloor = flat_mag(spectrum_of_target(xs, ys, p, gfloor), p)
    pf = profile(magfloor / sp)
    print("  C5 diffuse floor   top0.01=%.4f top0.05=%.4f Neff_frac=%.4f max/sqrt(p)=%.3f"
          % (pf["top0.01"], pf["top0.05"], pf["Neff_frac"], pf["max"]))

    # ---------------- C3 planted concentrated positive  (SPLIT INTO C3a / C3b -- see DEVIATIONS)
    # A target g lives on only n-1 ~ p curve points, so {U_g} spans an (n-1)-dim subspace of the
    # p^2 frequencies: NO realizable target can concentrate on 1% of S once p^2/100 > n-1.
    # C3a therefore tests the Arm-A DETECTOR on a synthetic magnitude array (prereg's literal
    # "synthetic U_plant(b,c)"); C3b tests Arm-B SEPARATION with a realizable target.
    nK = max(1, int(round(0.01 * (p * p - 1))))
    synth = np.full(p * p - 1, sp / 10.0)
    synth[rng.choice(p * p - 1, size=nK, replace=False)] = 4 * sp
    psyn = profile(synth / sp)
    c3_A = psyn["top0.01"] > 5 * pf["top0.01"]
    print("  C3a synth concentr top0.01=%.4f (floor %.4f) Neff_frac=%.4f -> Arm A detector %s"
          % (psyn["top0.01"], pf["top0.01"], psyn["Neff_frac"], "FIRED" if c3_A else "DID NOT FIRE"))

    b0, c0 = 3 % p, 5 % p
    gpl = np.exp(-2j * np.pi * ((b0 * np.array(xs[1:], dtype=np.int64)
                                 + c0 * np.array(ys[1:], dtype=np.int64)) % p) / p)
    magpl = flat_mag(spectrum_of_target(xs, ys, p, gpl), p)
    ppl = profile(magpl / sp)
    print("  C3b realizable     max/sqrt(p)=%.1f (floor max %.2f)  top0.01=%.4f  [Arm B check below]"
          % (ppl["max"], pf["max"], ppl["top0.01"]))

    # ---------------- ARM A
    pa = profile(mag / sp)
    print("  " + "-" * 108)
    print("  ARM A  character profile (normalized by sqrt(p)):")
    print("     top1%%=%.4f  top5%%=%.4f  top10%%=%.4f  top25%%=%.4f   Neff/|S|=%.4f"
          % (pa["top0.01"], pa["top0.05"], pa["top0.10"], pa["top0.25"], pa["Neff_frac"]))
    print("     q50=%.3f q90=%.3f q99=%.3f  max/sqrt(p)=%.3f   (ceiling 4+1/sqrt(p)=%.3f)"
          % (pa["q50"], pa["q90"], pa["q99"], pa["max"], 4 + 1 / sp))
    print("     FLOOR-RELATIVE: top1%% %.4f vs floor %.4f (ratio %.3f); Neff/|S| %.4f vs %.4f"
          % (pa["top0.01"], pf["top0.01"], pa["top0.01"] / max(pf["top0.01"], 1e-18),
             pa["Neff_frac"], pf["Neff_frac"]))

    # within-sector (chi3 class of b) profiles -- separates within- from between-sector
    bgrid = np.repeat(np.arange(p), p)
    cgrid = np.tile(np.arange(p), p)
    keep = ~((bgrid == 0) & (cgrid == 0))
    bK, cK = bgrid[keep], cgrid[keep]
    lab3 = s2_chi3(bK, cK, p, n)
    print("     within-sector (chi3 class of b):")
    for cl in (0, 1, 2):
        idx = lab3 == cl
        if idx.sum() < 10:
            continue
        ps = profile(mag[idx] / sp)
        print("        class %d  (%7d harmonics)  top1%%=%.4f  Neff/|S_c|=%.4f  max=%.3f  mean=%.4f"
              % (cl, int(idx.sum()), ps["top0.01"], ps["Neff_frac"], ps["max"],
                 float(np.mean(mag[idx] / sp))))

    # ---------------- ARM B  pattern vs random targets
    keys = ["top0.05", "Neff_frac", "max"]
    null = {k: [] for k in keys}
    ktop = max(1, int(round(0.05 * mag.size)))
    top_char = set(np.argsort(mag)[::-1][:ktop].tolist())
    jac_null = []
    prev_top = None
    for i in range(R_NULL):
        g = np.exp(2j * np.pi * rng.random(n - 1))
        mg = flat_mag(spectrum_of_target(xs, ys, p, g), p)
        pg = profile(mg / sp)
        for k in keys:
            null[k].append(pg[k])
        tg = set(np.argsort(mg)[::-1][:ktop].tolist())
        jac_null.append(len(top_char & tg) / len(top_char | tg))
        if prev_top is not None:
            pass
        prev_top = tg
    print("  " + "-" * 108)
    print("  ARM B  character vs R=%d random unit-phase targets (geometry, S, map held fixed)" % R_NULL)
    for k in keys:
        arr = np.array(null[k]); v = pa[k]
        ge = int((arr >= v).sum()); le = int((arr <= v).sum())
        pv = 2.0 * min(ge, le) / R_NULL
        print("     %-10s char=%.5f   null mean=%.5f sd=%.5f  two-sided rank p=%.4f%s"
              % (k, v, float(arr.mean()), float(arr.std()), min(pv, 1.0),
                 "  (resolution 1/R=%.3f)" % (1.0 / R_NULL)))
    ja = np.array(jac_null)
    print("     top-5%% support Jaccard(char, random): mean=%.4f sd=%.4f  (chance ~ f=0.05)"
          % (float(ja.mean()), float(ja.std())))

    # ARM B plant check: the C3 spike must be extreme on the same descriptors
    extreme = 0
    for k in keys:
        arr = np.array(null[k])
        if ppl[k] > arr.max() or ppl[k] < arr.min():
            extreme += 1
    c3_B = extreme >= 1
    print("     C3b plant vs same null: %d/%d descriptors outside the null range -> Arm B %s"
          % (extreme, len(keys), "FIRED" if c3_B else "DID NOT FIRE"))

    # ---------------- ARM C  d-free selectors
    print("  " + "-" * 108)
    print("  ARM C  d-free selectors vs |U(a0,b,c)|   (tautology guard asserted per selector)")
    order = np.argsort(mag)
    ranks = np.empty(mag.size, dtype=np.float64)
    ranks[order] = np.arange(1, mag.size + 1)
    for name, fn in SELECTORS:
        args = set(inspect.signature(fn).parameters.keys())
        assert args <= ALLOWED_ARGS, "TAUTOLOGY GUARD FAILED for %s: args=%s" % (name, args)
        lab = fn(bK, cK, p, n)
        if name == "s2_chi3":
            keepm = lab >= 0
            rr = ranks[keepm]
            o = np.argsort(rr); rk = np.empty(rr.size); rk[o] = np.arange(1, rr.size + 1)
            lb = lab[keepm]
            stat = kw_from_ranks(rk, lb, (0, 1, 2))
            nullv = []
            for _ in range(R_NULL):
                nullv.append(kw_from_ranks(rk, rng.permutation(lb), (0, 1, 2)))
            nullv = np.array(nullv)
            pv = (int((nullv >= stat).sum()) + 1) / (R_NULL + 1)
            print("     %-20s [args %s]  KW H=%9.3f   null mean=%7.3f sd=%6.3f  p=%.4f"
                  % (name, sorted(args), stat, float(nullv.mean()), float(nullv.std()), pv))
        else:
            if name == "s1_legendre":
                keepm = lab != 0
                b2 = (lab[keepm] > 0).astype(int)
                rr = ranks[keepm]
            else:
                keepm = np.ones(lab.size, dtype=bool)
                b2 = lab.astype(int)
                rr = ranks
            o = np.argsort(rr); rr2 = np.empty(rr.size); rr2[o] = np.arange(1, rr.size + 1)
            stat = auc_from_ranks(rr2, b2)
            nullv = []
            for _ in range(R_NULL):
                nullv.append(auc_from_ranks(rr2, rng.permutation(b2)))
            nullv = np.array(nullv)
            lo_, hi_ = float(np.quantile(nullv, 0.025)), float(np.quantile(nullv, 0.975))
            inband = lo_ <= stat <= hi_
            print("     %-20s [args %s]  AUC=%.5f   null 95%% band [%.5f, %.5f]  -> %s"
                  % (name, sorted(args), stat, lo_, hi_, "in-band" if inband else "OUT OF BAND"))
    return dict(p=p, n=n, c1=c1, c2=c2, c3_A=c3_A, c3_B=c3_B, pa=pa, pf=pf)


def main():
    sys.stdout.reconfigure(line_buffering=True)
    rng = np.random.default_rng(20260720)
    print("#" * 112)
    print("HARMONIC SUPPORT PATTERN v1 -- executes PREREG_harmonic_support_pattern_v1.md")
    print("SCOPE: enumerable model curves y^2=x^3+7 over small F_p ONLY.")
    print("       secp p=2^256-2^32-977 is NOT enumerable; NOTHING here transfers there.")
    print("OUTPUT TYPE: characterization + bounds with power and scope.  No ECDLP/security verdict.")
    print("#" * 112)
    res = []
    for lo, hi in PRIMES:
        r = run_prime(lo, hi, rng)
        if r:
            res.append(r)
    print("#" * 112)
    print("CONTROL SUMMARY (prereg section 5: no verdict on any arm if C3 fails)")
    print("#" * 112)
    for r in res:
        print("  p=%-6d C1=%-5s C2=%-5s C3_ArmA=%-5s C3_ArmB=%-5s"
              % (r["p"], r["c1"], r["c2"], r["c3_A"], r["c3_B"]))
    allok = all(r["c1"] and r["c2"] and r["c3_A"] and r["c3_B"] for r in res)
    print("  ALL CONTROLS FIRED: %s" % allok)
    if not allok:
        print("  -> prereg section 9 last row: NO RESULT REPORTED FOR ANY ARM.")
    print("#" * 112)
    print("ARM A trend across p (character vs its own diffuse floor):")
    print("  %-8s %-10s %-10s %-10s %-10s %-10s" % ("p", "top1%", "floor1%", "ratio", "Neff/|S|", "max/sqp"))
    for r in res:
        print("  %-8d %-10.4f %-10.4f %-10.3f %-10.4f %-10.3f"
              % (r["p"], r["pa"]["top0.01"], r["pf"]["top0.01"],
                 r["pa"]["top0.01"] / max(r["pf"]["top0.01"], 1e-18),
                 r["pa"]["Neff_frac"], r["pa"]["max"]))
    print("#" * 112)


main()
