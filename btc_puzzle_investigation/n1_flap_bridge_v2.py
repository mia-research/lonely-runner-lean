#!/usr/bin/env python3
"""
n1_flap_bridge_v2.py -- EXPLORATORY.  Repairs v1's statistic and adds instrument checks.

STATUS: [EXPLORATORY]. No experiment-designer pre-registration.  Nothing confirmatory.

WHAT v1 GOT WRONG
  * statistic |Vf|/|V1| is UNBOUNDED and blew up where |V1| ~ 0 (means of 2.1-2.8 for a "share").
    Replaced by a bounded rank correlation between the two power spectra.
  * v1 read the flap density against the cap law's 1/4.  That 1/4 is a density in the FUNDAMENTAL
    DOMAIN under uniform measure; mine is over the CURVE POINTS [d]G.  Different measures, so the
    comparison was never valid and the 0.14..0.30 spread convicts nothing.

WHAT v1 REVEALED (forced, carries zero information, but explains the design)
  * sum_d f(d) sigma(d) = 0 IDENTICALLY for p = 3 mod 4.  f(d)=chi2(y_[d]G) is ODD under d -> -d
    (chi2(-1) = -1 there), while sigma reads only x, and -P has the SAME x, so sigma is EVEN.
    The zero-frequency pairing is parity-forbidden on the whole SIN stratum.
    => any flap<->chi2 bridge must live at NONZERO frequency.  That is what V1(a), a != 0, is.

INSTRUMENT CHECKS (must pass before any number below is read)
  I1  sigma is constant on GLV orbits d -> lambda*d          (cap law Theorem B: sigma(beta x)=sigma(x))
  I2  the additive split V1 = Vf + Vc is exact
  I3  the exceptional-frequency count is 6x the mu6-class count from the decide script
CONTROL
  matched null permutes sigma ACROSS GLV ORBITS, preserving orbit structure and the value multiset
  -- so anything that survives is not merely "a mu3-invariant subset of this density".
"""
import sys, random
import numpy as np

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import is_prime, curve_order, ec_add, find_generator
from n1_flap_bridge_v1 import build, flap_sign

B = 7


def glv_lambda(p, n, G):
    """the scalar lambda with [lambda]P = (beta x, y);  lambda^3 = 1 mod n."""
    g = 2
    while pow(g, (p - 1) // 3, p) == 1:
        g += 1
    beta = pow(g, (p - 1) // 3, p)
    # locate lambda by matching the endomorphism on G
    tgt = (beta * G[0] % p, G[1])
    Q = None
    for d in range(n):
        if Q == tgt:
            return d, beta
        Q = ec_add(Q, G, p, B)
    raise RuntimeError("lambda not found")


def spearman(x, y):
    rx = np.argsort(np.argsort(x)).astype(float)
    ry = np.argsort(np.argsort(y)).astype(float)
    rx -= rx.mean(); ry -= ry.mean()
    return float((rx * ry).sum() / np.sqrt((rx * rx).sum() * (ry * ry).sum()))


def run(p, nrep=400, seed=17):
    n, f, sg = build(p)
    G = find_generator(p, n, B)
    lam, beta = glv_lambda(p, n, G)
    assert pow(lam, 3, n) == 1 and lam != 1, "lambda is not an order-3 scalar"

    # ---- I1 : sigma constant on GLV orbits
    bad = sum(1 for d in range(1, n) if sg[d] != sg[lam * d % n])
    # ---- spectra
    V1 = np.fft.fft(f)
    Sg = np.fft.fft(sg)
    inflap = (sg != 0).astype(np.int64)
    Vf = np.fft.fft(f * inflap)
    Vc = np.fft.fft(f * (1 - inflap))
    split_ok = np.max(np.abs(V1 - (Vf + Vc))) < 1e-6           # I2

    A = np.abs(V1[1:]) ** 2
    S = np.abs(Sg[1:]) ** 2
    rho = spearman(A, S)

    thr = (3 * p) ** 0.5
    exc = np.where(np.abs(V1[1:]) > thr)[0]                     # I3 (indices into 1..n-1)

    # targeted: is |FT(sigma)| anomalously large at the exceptional frequencies?
    Snorm = S / S.mean()
    obs_exc = float(Snorm[exc].mean()) if len(exc) else float("nan")

    # ---- matched null: permute sigma across GLV orbits
    rng = random.Random(seed)
    seen, orbits = set(), []
    for d in range(1, n):
        if d in seen:
            continue
        o = [d, lam * d % n, lam * lam * d % n]
        seen |= set(o)
        orbits.append(o)
    vals = [sg[o[0]] for o in orbits]
    rhos, excs = [], []
    for _ in range(nrep):
        vv = vals[:]
        rng.shuffle(vv)
        s2 = np.zeros(n, dtype=np.int64)
        for o, v in zip(orbits, vv):
            for d in o:
                s2[d] = v
        S2 = np.abs(np.fft.fft(s2)[1:]) ** 2
        rhos.append(spearman(A, S2))
        if len(exc):
            excs.append(float((S2 / S2.mean())[exc].mean()))

    rhos_s = sorted(rhos)
    p_rho = (sum(1 for x in rhos if abs(x) >= abs(rho)) + 1) / (nrep + 1)
    p_exc = ((sum(1 for x in excs if x >= obs_exc) + 1) / (nrep + 1)) if excs else float("nan")

    print(f"p={p:<5} n={n:<5} lambda={lam:<6} orbits={len(orbits):<5} "
          f"exceptional freqs={len(exc)}")
    print(f"   I1 sigma GLV-invariant : {'PASS' if bad == 0 else f'FAIL ({bad} of {n-1})'}"
          f"    I2 split exact : {'PASS' if split_ok else 'FAIL'}")
    print(f"   spectra rank-corr(|V1|^2, |FT sigma|^2) = {rho:+.4f}   "
          f"null median {rhos_s[nrep//2]:+.4f}   two-sided p = {p_rho:.4f}")
    if len(exc):
        print(f"   |FT sigma|^2 at exceptional freqs (normalised) = {obs_exc:.4f}   "
              f"null median {sorted(excs)[nrep//2]:.4f}   one-sided p = {p_exc:.4f}")
    return dict(p=p, rho=rho, p_rho=p_rho, obs_exc=obs_exc, p_exc=p_exc,
                i1=(bad == 0), nexc=len(exc))


if __name__ == "__main__":
    print("[EXPLORATORY] no prereg; nothing here is confirmatory\n")
    out = []
    for p in [int(t) for t in sys.argv[1:]]:
        out.append(run(p)); print()
    print("=" * 72)
    print("SUMMARY  (p-values are per-prime; no pooling claimed)")
    print("%6s %8s %9s %10s %9s %6s" % ("p", "rho", "p(rho)", "exc-power", "p(exc)", "I1"))
    for r in out:
        print("%6d %+8.4f %9.4f %10.4f %9.4f %6s"
              % (r["p"], r["rho"], r["p_rho"], r["obs_exc"], r["p_exc"], "ok" if r["i1"] else "FAIL"))
