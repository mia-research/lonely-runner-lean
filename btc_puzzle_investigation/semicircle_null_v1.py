#!/usr/bin/env python3
"""
semicircle_null_v1.py -- the CAP-RESPECTING, MARGINAL-VARYING null, and the
statistics it unblocks.  EXPLORATORY.  No verdict, no grade, no leakage claim.

THE BLOCKER IT REMOVES (RESULT_theta_structure_v1.md Sec 4, RESULT_phase_family_and_tail_v1.md
Sec 3b).  Two nulls existed and NEITHER can test a |V|-marginal statistic:
  * frequency-domain class permutation -- preserves the |V| multiset EXACTLY, so it has
    ZERO power against spacings, order statistics, Delta_3, Sigma^2, the whole Katz-Sarnak
    family, and the entire upper tail;
  * signal-domain permutation -- VIOLATES the proved cap (top-5 |V|/sqrt p = 2.74-3.25
    against a ceiling of 2), so its tail comparisons are forced artifacts.

THE CONSTRUCTION.  u(a) = V(a)/(2i sqrt p) is real, and the record's own two moment
facts pin its marginal exactly:
      E[u^2] = 1/4   (FORCED, Parseval)          E[u^4] = 1/8   (measured, = full SU(2))
The semicircle law on [-1,1], density (2/pi) sqrt(1-u^2), has moments
      m_2k = Catalan(k)/4^k  =>  m_2 = 1/4,  m_4 = 2/16 = 1/8.
Both match.  Equivalently u = cos(theta) with theta ~ (2/pi) sin^2(theta) d theta -- the
SATO-TATE measure.  So the null is:

      u(a) iid SEMICIRCLE on [-1,1], rebuilt through the forced mu3 + odd symmetry.

  * CAP-RESPECTING by construction: |u| <= 1, i.e. |V| <= 2 sqrt p.  [the proved ceiling]
  * MARGINAL-VARYING: every draw is a fresh multiset  => nonzero power on order statistics.
  * It IS the Katz-Sarnak / Sato-Tate prediction the record cites and has never used.

FREE INDEX SET.  mu3-invariance + oddness make only L = (n-1)/6 values free; the other
n-1 values are 6 exact copies.  Statistics MUST be run on the L free values or the 6-fold
degeneracy swamps every spacing.  (Both data and null use the same L free representatives.)

STATISTICS UNBLOCKED (all |V|-marginal, all previously untestable)
  S1 SPACINGS   unfold u through the semicircle CDF -> uniform; nearest-neighbour spacings
                should be Exp(1) under iid.  KS distance.  Repulsion or clustering = signal.
  S2 SIGMA^2    number variance in unfolded windows; iid => Sigma^2(l) = l(1 - l/L).
  S3 TAIL       max|u|, top-5 mean, and the count above 0.95 -- where a caustic would pile
                up against the cap.
  S4 SMALLBALL  count below 0.05 -- the low-tail the Rayleigh-vs-real question turns on.

Exact int signal path (legendre/orbit/index maps); float only in the statistics, ranked
against null draws.
"""
import argparse, json, sys
import numpy as np
from sympy import primitive_root
from twist_orbit_spectrum_run_v1 import signal


# ------------------------------------------------------------------ free index set
def free_reps(n):
    """The L = (n-1)/6 representatives g^0..g^(L-1) of (Z/n)^* / mu6, and g."""
    g = int(primitive_root(n))
    L = (n - 1) // 6
    reps = np.empty(L, dtype=np.int64)
    cur = 1
    for m in range(L):
        reps[m] = cur
        cur = (cur * g) % n
    return reps, L


def u_free(p, n, c, reps):
    """The L free values of u(a) = V(a)/(2i sqrt p)."""
    V = np.fft.fft(c.astype(np.complex128))                     # noqa: float
    return (V[reps] / (2j * np.sqrt(p))).real                   # noqa: float


# ------------------------------------------------------------------ the null
def semicircle(L, rng):
    """iid semicircle on [-1,1]: u = cos(theta), theta ~ (2/pi) sin^2 theta.
    Rejection: propose theta ~ U[0,pi], accept w.p. sin^2(theta).  Acceptance 1/2."""
    out = np.empty(L)                                           # noqa: float
    got = 0
    while got < L:
        m = 2 * (L - got) + 16
        th = rng.uniform(0.0, np.pi, size=m)                    # noqa: float
        acc = th[rng.random(m) < np.sin(th) ** 2]               # noqa: float
        k = min(len(acc), L - got)
        out[got:got + k] = np.cos(acc[:k])                      # noqa: float
        got += k
    return out


# ------------------------------------------------------------------ statistics
def _unfold(u):
    """Semicircle CDF -> uniform on [0,1].  F(u) = 1/2 + (u sqrt(1-u^2) + arcsin u)/pi."""
    u = np.clip(u, -1.0, 1.0)
    return 0.5 + (u * np.sqrt(1 - u * u) + np.arcsin(u)) / np.pi   # noqa: float


def S1_spacing_ks(u):
    """KS distance of normalised nearest-neighbour spacings to Exp(1)."""
    x = np.sort(_unfold(u))
    s = np.diff(x)
    if s.size < 8 or s.mean() <= 0:
        return 0.0
    s = np.sort(s / s.mean())
    emp = np.arange(1, s.size + 1) / s.size
    cdf = 1 - np.exp(-s)                                        # noqa: float
    return float(max(np.max(np.abs(emp - cdf)),
                     np.max(np.abs(cdf - (np.arange(s.size) / s.size)))))


def S2_sigma2(u, ell=8.0):
    """Number variance in unfolded windows of mean occupancy `ell`."""
    x = np.sort(_unfold(u))
    L = x.size
    w = ell / L
    starts = np.linspace(0.0, 1.0 - w, 400)
    cnt = np.searchsorted(x, starts + w) - np.searchsorted(x, starts)
    return float(cnt.var())                                     # noqa: float


def S3_tail(u):
    a = np.abs(u)
    s = np.sort(a)
    return float(s[-1]), float(s[-5:].mean()), float((a > 0.95).mean())   # noqa: float


def S4_smallball(u):
    return float((np.abs(u) < 0.05).mean())                     # noqa: float


def allstats(u):
    mx, t5, hi = S3_tail(u)
    return {"S1_ks": S1_spacing_ks(u), "S2_sig2": S2_sigma2(u),
            "S3_max": mx, "S3_top5": t5, "S3_frac_gt95": hi,
            "S4_frac_lt05": S4_smallball(u)}


KEYS = ["S1_ks", "S2_sig2", "S3_max", "S3_top5", "S3_frac_gt95", "S4_frac_lt05"]


def run(p, R, rng):
    s = signal(p, 7)
    if s is None:
        return None
    n, c, X, Y = s
    reps, L = free_reps(n)
    u = u_free(p, n, c, reps)
    # ---- controls ---------------------------------------------------------
    cap = bool(np.max(np.abs(u)) <= 1.0 + 1e-9)
    m2, m4 = float(np.mean(u ** 2)), float(np.mean(u ** 4))     # noqa: float
    d = allstats(u)
    nulls = {k: [] for k in KEYS}
    for _ in range(R):
        un = semicircle(L, rng)
        sn = allstats(un)
        for k in KEYS:
            nulls[k].append(sn[k])
    o = {"p": p, "n": int(n), "L": int(L), "C_CAP": cap, "m2": m2, "m4": m4}
    print(f"p={p:5d} n={n:5d} L={L:5d}  C_CAP={cap}  E[u^2]={m2:.4f} (¼)  "
          f"E[u^4]={m4:.4f} (⅛)")
    for k in KEYS:
        arr = np.array(nulls[k])
        # two-sided rank p-value
        ge = int((arr >= d[k]).sum()); le = int((arr <= d[k]).sum())
        pv = 2.0 * min(ge + 1, le + 1) / (R + 1)                # noqa: float
        pv = min(pv, 1.0)
        o[k] = {"data": d[k], "null_mean": float(arr.mean()),   # noqa: float
                "null_sd": float(arr.std()), "p2": float(pv)}   # noqa: float
        z = (d[k] - arr.mean()) / (arr.std() + 1e-15)           # noqa: float
        print(f"   {k:14s} data {d[k]:9.5f}   null {arr.mean():9.5f} "
              f"+-{arr.std():8.5f}   z={z:+6.2f}  p2={pv:.4f}")
    sys.stdout.flush()
    return o


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=int, nargs="+", default=[823, 1303, 1831, 2251, 2731])
    ap.add_argument("-R", type=int, default=400)
    ap.add_argument("--seed", type=int, default=20260730)
    ap.add_argument("--out", default="semicircle_null_v1.json")
    a = ap.parse_args()
    rng = np.random.default_rng(a.seed)
    res = [r for r in (run(p, a.R, rng) for p in a.primes) if r]
    json.dump(res, open(a.out, "w"), indent=1)
    print(f"\nwrote {a.out}")


if __name__ == "__main__":
    main()
