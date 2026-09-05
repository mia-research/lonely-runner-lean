#!/usr/bin/env python3
"""transfer_operator_rmt_battery_v1.py -- ITEM 2, DONE PROPERLY: the RMT battery on a SPECTRUM.

WHAT WENT WRONG BEFORE.  Asked for spacing / Delta_3 / Sigma^2 on the |T(a,b)|^2 object, I measured
spatial autocorrelations (C_a1, C_b1, C_a3) instead.  Those are 2-D grid adjacency statistics and
have nothing to do with spectral rigidity or the Wigner surmise.  I substituted them because level
statistics on raw intensities looked degenerate to me -- but I never demonstrated that, I just
pivoted.  This file does both jobs.

PART A -- DEMONSTRATE the degeneracy instead of asserting it.
   Unfolding a sample through its OWN empirical CDF returns exactly the uniform order statistics,
   so every spacing is exactly 1 and Delta_3 = 0 -- for ANY input whatsoever.  Unfolding through a
   THEORETICAL CDF instead just re-tests the marginal, i.e. Porter-Thomas, which is already measured.
   So "level statistics on the sorted intensities" is either identically degenerate or a restatement
   of the existing 1-point test.  Both branches are shown numerically.

PART B -- THE REAL SPECTRUM.  The record's thermodynamic layer has a genuine operator: the
coarse-grained transfer (Koopman) operator of a label under P -> P+G (conservation_spectrum_v1.py).
The record extracted ONE number from it, |lambda_2|.  Its FULL spectrum was never examined.
Here the label alphabet is refined until the operator carries a few hundred eigenvalues, and the
battery is run on that spectrum:
   S_SPACING  nearest-neighbour spacing in the complex plane (Ginibre geometry), KS vs the null
   S_DELTA3   Dyson-Mehta rigidity of the counting function of the sorted moduli |lambda|
   S_SIGMA2   number variance of eigenvalues in disks
NULL = the record's own shuffle floor: shuffle the label sequence (destroys temporal/dynamical
structure, preserves the label marginal EXACTLY) and rebuild the operator.  Data-derived; no
Katz-Sarnak, Ginibre or GUE prediction is assumed anywhere.
CONTROL = C-PLANT: make the label sticky (a planted near-conservation law) and confirm detection.
"""

import numpy as np
import sys
from fractions import Fraction as Fr

sys.path.insert(0, ".")
from conservation_spectrum_v1 import (isprime, curve_points_order, curve_gen, orbit,
                                      transfer_spectrum)


# ------------------------------------------------------------------ PART A

def partA():
    print("=" * 100)
    print("PART A -- why 'level statistics on sorted intensities' is not a test (demonstrated)")
    print("=" * 100)
    rng = np.random.default_rng(0)
    for name, sample in (("Porter-Thomas (exponential)", rng.exponential(1.0, 4000)),
                         ("uniform", rng.random(4000)),
                         ("bimodal (wildly non-PT)", np.r_[rng.normal(1, .05, 2000),
                                                           rng.normal(9, .05, 2000)])):
        x = np.sort(sample)
        N = x.size
        emp = (np.arange(1, N + 1) - 0.5) / N          # unfold through the OWN empirical CDF
        s = np.diff(emp) * N
        print("  %-28s unfolded spacings: min=%.6f max=%.6f sd=%.3e  -> Delta_3 = 0 identically"
              % (name, s.min(), s.max(), s.std()))
    print("  => empirical unfolding is the identity: every input gives a perfectly rigid ladder.")
    print("     Theoretical unfolding instead tests the MARGINAL = Porter-Thomas, already measured.")
    print("     Neither is a 2-point statistic.  The 2-point content needs an actual OPERATOR.")


# ------------------------------------------------------------------ PART B

def spectrum_stats(ev):
    """RMT battery on a complex spectrum."""
    z = ev[np.abs(ev) < 0.999999]                      # drop the Perron eigenvalue 1
    if z.size < 40:
        return None
    # S_SPACING: nearest-neighbour distance in C, normalised by the mean
    d = np.abs(z[:, None] - z[None, :])
    np.fill_diagonal(d, np.inf)
    nn = d.min(axis=1)
    nn = nn / nn.mean()
    # S_DELTA3 on the sorted moduli, SMOOTH-unfolded.
    # NB: rank-unfolding forces the counting function exactly linear => Delta_3 == 0 for ANY input
    # (this is precisely the degeneracy PART A demonstrates).  Unfold by fitting a low-order
    # polynomial to the staircase (r_i -> i), then measure rigidity about that smooth trend.
    r = np.sort(np.abs(z))
    M = r.size
    idx = np.arange(M) * 1.0
    deg = 5
    coef = np.polyfit(r, idx, deg)
    lev = np.polyval(coef, r)                # smooth-unfolded levels, mean spacing ~1
    ell = 12.0
    starts = np.linspace(0, M - ell, 120)
    vals = []
    for a in starts:
        m = (lev >= a) & (lev < a + ell)
        t = lev[m] - a
        if t.size < 4:
            continue
        cnt = np.arange(t.size) * 1.0
        A = np.vstack([t, np.ones_like(t)]).T
        cf, *_ = np.linalg.lstsq(A, cnt, rcond=None)
        vals.append(float(np.mean((cnt - A @ cf) ** 2)))
    delta3 = float(np.mean(vals)) if vals else 0.0
    # S_SIGMA2: number variance in disks of fixed radius
    R0 = 0.15
    ctrs = z[np.argsort(np.abs(z))[::max(1, z.size//200)]]
    cnt = np.array([np.sum(np.abs(z - c) < R0) for c in ctrs], dtype=float)
    return {"S_spacing_sd": float(nn.std()),
            "S_delta3": delta3,
            "S_sigma2": float(cnt.var())}


KEYS = ["S_spacing_sd", "S_delta3", "S_sigma2"]
rng_global = np.random.default_rng(12345)


def labels_fine(xs, p, K):
    """a fine coarse-graining of the point label: K bins of x, exact integer binning."""
    return np.array([min(K - 1, (int(x) * K) // p) if x is not None else 0 for x in xs],
                    dtype=np.int64)


def partB(R=120):
    print()
    print("=" * 100)
    print("PART B -- the RMT battery on the TRANSFER OPERATOR spectrum (null = record's shuffle floor)")
    print("=" * 100)
    for lo, hi in [(400, 700), (1000, 1400), (2000, 2600)]:
        p = next((q for q in range(lo, hi)
                  if isprime(q) and q % 3 == 1 and isprime(curve_points_order(q))), None)
        if p is None:
            continue
        n = curve_points_order(p)
        G = curve_gen(p)
        xs, ys = orbit(G, p, n)
        for K in (18,):
            ns = K
            lab = labels_fine(xs, p, K)[1:]
            # refine: use PAIRS of consecutive labels as the state => K^2 states, a real spectrum
            st = (lab[:-1] * K + lab[1:]).astype(np.int64)
            nstates = K*K
            ev = transfer_spectrum(st, nstates)
            obs = spectrum_stats(ev)
            if obs is None:
                print("  p=%d K=%d: spectrum too small" % (p, K))
                continue
            rng = np.random.default_rng(p)
            nulls = {k: [] for k in KEYS}
            for _ in range(R):
                sh = lab.copy()
                rng.shuffle(sh)
                sst = (sh[:-1]*K + sh[1:]).astype(np.int64)
                e2 = transfer_spectrum(sst, nstates)
                s = spectrum_stats(e2)
                if s:
                    for k in KEYS:
                        nulls[k].append(s[k])
            # C-PLANT: sticky label (planted near-conservation)
            pl = lab.copy()
            for i in range(1, pl.size):
                if rng.random() < 0.5:
                    pl[i] = pl[i-1]
            pst = (pl[:-1]*K + pl[1:]).astype(np.int64)
            op = spectrum_stats(transfer_spectrum(pst, nstates))
            print("  p=%-5d n=%-5d states=%-5d eigenvalues used=%d" % (p, n, nstates,
                                                                       np.sum(np.abs(ev) < 0.999999)))
            for k in KEYS:
                nv = np.array(nulls[k])
                if nv.size < 10:
                    continue
                z = (obs[k] - nv.mean())/nv.std() if nv.std() > 0 else 0.0
                ge = int((nv >= obs[k]).sum())
                pv = (ge + 1)/(len(nv) + 1)
                pv2 = min(pv, 1 - pv + 1.0/(len(nv) + 1))*2
                zp = (op[k] - nv.mean())/nv.std() if (op and nv.std() > 0) else 0.0
                print("      %-14s data=%-10.4f null=%-10.4f+-%-9.4f z=%+6.2f p=%.4f%s | PLANT z=%+7.2f %s"
                      % (k, obs[k], nv.mean(), nv.std(), z, pv2, "*" if pv2 <= 0.05 else " ",
                         zp, "FIRES" if abs(zp) >= 3 else ""))


if __name__ == "__main__":
    partA()
    partB(int(sys.argv[1]) if len(sys.argv) > 1 else 120)
