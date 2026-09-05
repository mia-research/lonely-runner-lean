#!/usr/bin/env python3
"""rmt_delta3_twopoint_v1.py -- ITEM 2: the RMT statistics that are ACTUALLY still unmeasured.

STALE-TABLE CORRECTION FIRST.  SYNTHESIS_brainstorm_seven_cycles_ADDENDUM_1_v1.md Sec 4 lists four
random-matrix statistics as "never measured" on {theta_a}:
    level spacing (Wigner) | spectral rigidity Delta_3 | number variance Sigma^2 | two-point corr.
That file is dated **Jul 26**.  RESULT_semicircle_null_and_verification_v1.md (**Jul 30**) ran
S1 = spacing KS and S2 = number variance Sigma^2 against the cap-respecting semicircle null, at 17
primes + 15 OOS, and both are NULL.  So TWO of the four were measured four days after the table was
written -- the recurring "an item marked OPEN post-dates its own answer" pattern.

STILL GENUINELY UNRUN on {theta_a}, and run here:
    S5  spectral rigidity Delta_3(L)   -- Dyson-Mehta; least-squares straight-line fit to the
                                          unfolded counting function, averaged over windows.
    S6  two-point correlation, via the spectral FORM FACTOR K(tau) (its Fourier transform) and the
                                          short-range pair-correlation excess.

NULL.  The same cap-respecting, marginal-varying iid-semicircle null the Jul-30 work built -- it IS
the Katz-Sarnak/Sato-Tate prediction.  Statistics run on the L = (n-1)/6 FREE class representatives;
the other n-1 values are 6 exact copies and their degeneracy swamps every spacing.

CONTROLS.  C-PLANT: a rigid (picket-fence) spectrum and a clustered spectrum must both be detected
by Delta_3 -- a rigidity statistic that cannot see a rigid or a clustered spectrum is not measuring
rigidity.  Reported before any verdict.

Floats appear only as monotone statistics ranked against the matched null (permitted).
"""

import numpy as np
import sys
from semicircle_null_v1 import signal, free_reps, u_free, semicircle, _unfold


# --------------------------------------------------------------- new statistics

def S5_delta3(u, ell=15.0, nwin=200):
    """Dyson-Mehta spectral rigidity Delta_3 at window length `ell` (in mean spacings).
       For unfolded levels x in [0,1] scaled to mean spacing 1, Delta_3(L) is the
       least-squares deviation of the counting function from a straight line, averaged
       over windows.  Computed exactly for the piecewise-constant N(x)."""
    x = np.sort(_unfold(u)) * u.size          # scale to mean spacing 1
    N = x.size
    if N < 4 * ell:
        return 0.0
    starts = np.linspace(0.0, N - ell, nwin)
    vals = []
    for a in starts:
        b = a + ell
        xi = x[(x >= a) & (x < b)] - a        # levels inside, shifted to [0, ell]
        k0 = int(np.searchsorted(x, a))       # count below the window
        # N(t) on [0,ell] = k0 + #{xi <= t}; drop the constant k0 into the intercept
        # exact integrals of the step function s(t) = #{xi <= t}
        m = xi.size
        if m == 0:
            vals.append(0.0)
            continue
        # s(t) = sum_j 1[t >= xi_j]
        I0 = np.sum(ell - xi)                                   # int_0^ell s dt
        I1 = np.sum((ell**2 - xi**2) / 2.0)                     # int_0^ell t*s dt
        # int s^2 dt : s is a staircase; on [xi_j, xi_{j+1}) s = j+1
        xs = np.concatenate([xi, [ell]])
        seg = np.diff(xs)
        lev = np.arange(1, m + 1)
        I2 = float(np.sum(seg * lev * lev))
        # least squares fit A*t + B to s(t) on [0,ell]
        M00, M01, M11 = ell, ell**2 / 2.0, ell**3 / 3.0
        det = M00 * M11 - M01 * M01
        B = (M11 * I0 - M01 * I1) / det
        A = (M00 * I1 - M01 * I0) / det
        resid = I2 - 2 * (A * I1 + B * I0) + (A * A * M11 + 2 * A * B * M01 + B * B * M00)
        vals.append(max(resid, 0.0) / ell)
    return float(np.mean(vals))


def S6_formfactor(u, taus=(0.05, 0.10, 0.20)):
    """Spectral form factor K(tau) = |sum_j exp(2*pi*i*tau*x_j)|^2 / N on unfolded levels.
       This is the Fourier transform of the two-point correlation function."""
    x = np.sort(_unfold(u)) * u.size
    N = x.size
    out = []
    for t in taus:
        z = np.exp(2j * np.pi * t * x).sum()
        out.append(float((z.real**2 + z.imag**2) / N))
    return out


def S6b_paircorr(u, rmax=3.0, nb=6):
    """short-range pair-correlation excess: density of unfolded level differences in
       (0, rmax] relative to the uniform expectation."""
    x = np.sort(_unfold(u)) * u.size
    N = x.size
    d = []
    for k in range(1, min(12, N)):
        d.append(x[k:] - x[:-k])
    d = np.concatenate(d)
    d = d[d <= rmax]
    h, _ = np.histogram(d, bins=nb, range=(0.0, rmax))
    exp = N * (rmax / nb)                     # uniform expectation per bin (mean spacing 1)
    return float(np.sum((h - exp)**2) / (nb * exp * exp))


def stats_of(u):
    ff = S6_formfactor(u)
    return {"S5_delta3": S5_delta3(u),
            "S6_K005": ff[0], "S6_K010": ff[1], "S6_K020": ff[2],
            "S6b_paircorr": S6b_paircorr(u)}


KEYS = ["S5_delta3", "S6_K005", "S6_K010", "S6_K020", "S6b_paircorr"]


def run_prime(p, R, rng):
    sig = signal(p, 7)
    if sig is None:
        return None
    n, c, _X, _Y = sig
    reps, L = free_reps(n)
    u = u_free(p, n, c, reps)
    obs = stats_of(u)
    ge = {k: 0 for k in KEYS}
    for _ in range(R):
        un = semicircle(L, rng)
        s = stats_of(un)
        for k in KEYS:
            if s[k] >= obs[k]:
                ge[k] += 1
    return n, L, obs, ge


def controls(L, rng, R=200):
    """C-PLANT: Delta_3 must separate a RIGID (picket-fence) and a CLUSTERED spectrum
       from the semicircle null.  If it cannot, it is not measuring rigidity."""
    from numpy import pi
    print("  C-PLANT (L=%d levels, R=%d null draws)" % (L, R))
    # rigid: perfectly equispaced in unfolded coordinate -> map back through the CDF
    q = (np.arange(L) + 0.5) / L
    # invert the semicircle CDF numerically on a fine grid
    grid = np.linspace(-1.0, 1.0, 200001)
    F = _unfold(grid)
    u_rigid = np.interp(q, F, grid)
    # clustered: two tight clumps
    u_clust = np.interp(np.concatenate([np.linspace(0.02, 0.18, L // 2),
                                        np.linspace(0.62, 0.78, L - L // 2)]), F, grid)
    nulls = [stats_of(semicircle(L, rng)) for _ in range(R)]
    for lab, uu in (("RIGID picket-fence", u_rigid), ("CLUSTERED two-clump", u_clust)):
        s = stats_of(uu)
        line = []
        for k in KEYS:
            ge = sum(1 for z in nulls if z[k] >= s[k])
            lo = sum(1 for z in nulls if z[k] <= s[k])
            pv = (min(ge, lo) + 1) / (R + 1)
            line.append("%s p=%.4f%s" % (k, pv, "*" if pv <= 0.05 else ""))
        print("     %-20s %s" % (lab, " | ".join(line)))


if __name__ == "__main__":
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    rng = np.random.default_rng(20260801)
    PRIMES = [823, 1051, 1471, 1723, 2089, 2311, 2647, 3011, 3499, 4051, 4483, 4831]
    print("=" * 100)
    print("ITEM 2 -- Delta_3 and the two-point correlation on {theta_a} (the two genuinely unrun)")
    print("=" * 100)
    n0, c0, _a, _b = signal(PRIMES[4], 7)
    _, L0 = free_reps(n0)
    controls(L0, rng)
    print()
    print("  %-7s %-7s %-7s | %s" % ("p", "n", "L", "  ".join("%-14s" % k for k in KEYS)))
    tally = {k: [] for k in KEYS}
    for p in PRIMES:
        rp = run_prime(p, R, rng)
        if rp is None:
            print("  %-7d  (no j=0 cyclic curve)" % p)
            continue
        n, L, obs, ge = rp
        cells = []
        for k in KEYS:
            pv = (ge[k] + 1) / (R + 1)
            pv2 = min(pv, 1 - pv + 1.0 / (R + 1)) * 2
            tally[k].append(pv2)
            cells.append("%-14s" % ("%.4f%s" % (pv2, "*" if pv2 <= 0.05 else "")))
        print("  %-7d %-7d %-7d | %s" % (p, n, L, "  ".join(cells)))
    print()
    print("  two-sided p <= 0.05 counts (expected %.1f of %d per statistic):"
          % (0.05 * len(PRIMES), len(PRIMES)))
    for k in KEYS:
        hits = sum(1 for v in tally[k] if v <= 0.05)
        print("     %-14s %d/%d" % (k, hits, len(PRIMES)))
