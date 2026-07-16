#!/usr/bin/env python3
"""
substrate_crossdomain_v1.py -- Item #5 (exploratory bet): does the secp thermal/critical/single-well
(random-matrix / GUE) lens transfer to the phi-residue RH objects and LRC?  Tests "one programme"
rather than asserting it.

SOURCE (read first): the user's "Self-Adjoint Realization of the Berry-Keating Operator with
phi(n)-Residue Structure" derives the phi(n)-residue structure DIRECTLY from the Lonely Runner setup:
  * Def 1.1: arithmetic-progression runners v_i = v0+(i-1)d
  * Def 1.2: uniform separation min_{i<j} d(theta_i,theta_j) >= 1/n
  * Thm 1.1: uniform separation occurs at EXACTLY phi(n) times (coprime residues r, gcd(r,n)=1)
  * that phi(n)-coprimality => Berry-Keating operator boundary conditions => spectrum {pi n^2}
    => theta function => Riemann xi(s) functional equation.

DISCRIMINATOR: nearest-neighbor level-spacing statistics (normalized to mean 1). Level repulsion
P(s->0) separates the substrates:
  * GUE (chaotic/thermal): P(s)=(32/pi^2)s^2 e^{-4s^2/pi}; strong repulsion, P(s<0.1)~0.001.
  * Poisson (uncorrelated):  P(s)=e^{-s};                  P(s<0.1)~0.095.
  * picket-fence (rigid/integrable): all s=1;              P(s<0.1)=0.

OBJECTS:
  (RH, chaotic end)   Riemann zeta zeros (mpmath) -- expect GUE [Montgomery-Odlyzko, CITED].
  (RIGID end, operator) Berry-Keating phi(n)-residue spectrum {pi n^2} -- analytic picket-fence.
  (RIGID end, LRC)    totatives {r/n : gcd(r,n)=1} (the phi(n) uniform-separation residues) -- arithmetic.
  (chaotic end, secp) |T(a,b)|^2 Porter-Thomas -- CITED v18 (chaotic/thermal), anchor.

Float carve-out: analytic-size spectral statistics; no key / no signal path.
"""
import math
import numpy as np
from mpmath import mp, zetazero


def nn_stats(spacings):
    """normalized (mean-1) nearest-neighbor spacings -> (P(s<0.1), P(s<0.5), mean, cv)."""
    s = np.asarray(spacings, dtype=float)
    s = s / s.mean()
    return (float(np.mean(s < 0.1)), float(np.mean(s < 0.5)), float(s.mean()), float(s.std()))


def zeta_zero_spacings(N=300):
    mp.dps = 25
    g = np.array([float(zetazero(k).imag) for k in range(1, N + 1)])
    # unfold by the smooth density: N(T) ~ (T/2pi) log(T/2pi) - T/2pi
    def unf(t):
        return (t / (2 * math.pi)) * (math.log(t / (2 * math.pi)) - 1)
    u = np.array([unf(t) for t in g])
    return np.diff(u)


def totative_spacings(n):
    tot = [r for r in range(1, n) if math.gcd(r, n) == 1]
    pts = np.array(tot, dtype=float) / n
    return np.diff(np.sort(pts))          # gaps between consecutive coprime residues in [0,1)


def bk_spectrum_spacings(N=400):
    """Berry-Keating phi(n)-residue spectrum {pi k^2}; unfold by Weyl density (sqrt spectrum)."""
    lam = np.array([math.pi * k * k for k in range(1, N + 1)])
    # counting function N(L) = #{k: pi k^2 <= L} = floor(sqrt(L/pi)); unfold u = sqrt(lam/pi) = k
    u = np.sqrt(lam / math.pi)
    return np.diff(u)                      # all == 1 exactly (picket fence)


def references():
    # reference P(s<0.1), P(s<0.5) for the three universality classes (analytic)
    # GUE Wigner surmise
    from scipy.integrate import quad
    gue = lambda s: (32/math.pi**2)*s*s*math.exp(-4*s*s/math.pi)
    g01 = quad(gue, 0, 0.1)[0]; g05 = quad(gue, 0, 0.5)[0]
    p01 = 1-math.exp(-0.1); p05 = 1-math.exp(-0.5)
    return dict(GUE=(g01, g05), Poisson=(p01, p05), picket=(0.0, 0.0))


def main():
    print("="*82)
    print("SUBSTRATE CROSS-DOMAIN BET -- item #5: does secp's GUE/thermal lens transfer to RH & LRC?")
    print("="*82)
    ref = references()
    print("\n reference NN-spacing classes:  (P(s<0.1), P(s<0.5))")
    for k, (a, b) in ref.items():
        print("   %-8s P(s<0.1)=%.3f  P(s<0.5)=%.3f" % (k, a, b))

    print("\n [CHAOTIC end] Riemann zeta zeros (first 300) -- expect GUE (Montgomery-Odlyzko)")
    zs = zeta_zero_spacings(300)
    p01, p05, m, cv = nn_stats(zs)
    print("   zeta zeros:  P(s<0.1)=%.3f  P(s<0.5)=%.3f  mean=%.3f  cv=%.3f  -> %s"
          % (p01, p05, m, cv, "GUE (level repulsion)" if p01 < 0.03 else "not GUE"))

    print("\n [RIGID end, operator] Berry-Keating phi(n)-residue spectrum {pi k^2} -- picket-fence")
    bk = bk_spectrum_spacings(400)
    p01, p05, m, cv = nn_stats(bk)
    print("   {pi k^2}:    P(s<0.1)=%.3f  P(s<0.5)=%.3f  mean=%.3f  cv=%.3f  -> picket-fence (all s=1, rigid)"
          % (p01, p05, m, cv))

    print("\n [RIGID end, LRC] totatives {r/n: gcd(r,n)=1} = the phi(n) uniform-separation residues")
    print("   (discriminator: a HARD min-gap + P(s<0.3)=0 = arithmetic hard-gap, NOT GUE's soft repulsion)")
    for n in [2310, 30030, 510510]:   # 2*3*5*7*11, *13, *17 -- highly composite
        ts = totative_spacings(n)
        s = np.asarray(ts, float); s = s / s.mean()
        mingap = float(s.min()); p03 = float(np.mean(s < 0.3)); cv = float(s.std())
        # GUE has soft repulsion: min-gap ~ 0 and P(s<0.3) > 0.  A hard gap means min-gap >> 0, P(s<0.3)=0.
        cls = "GUE (soft repulsion)" if (mingap < 0.15 and p03 > 0.005) else \
              ("picket-fence" if cv < 0.05 else "ARITHMETIC HARD-GAP (not GUE, not Poisson)")
        print("   n=%-7d (phi=%d): min-gap=%.3f  P(s<0.3)=%.3f  cv=%.3f  -> %s"
              % (n, sum(1 for r in range(1, n) if math.gcd(r, n) == 1), mingap, p03, cv, cls))

    print("\n [CHAOTIC end, secp] |T(a,b)|^2 ~ Porter-Thomas (exponential intensities), rigid tail")
    print("   CITED v18: E[I^2]=2.00, E[I^3]=5.97, E[I^4]=22.7 (Porter-Thomas) -> chaotic/thermal (GUE class).")

    print("\n VERDICT (framing bet, EMPIRICAL/CITED -- not a theorem):")
    print("   The programme spans TWO opposite substrates, bridged by the theta/Mellin/Hecke construction:")
    print("   * CHAOTIC/thermal/GUE:  secp Frobenius (Weil), Riemann zeta ZEROS (Montgomery-Odlyzko).")
    print("   * RIGID/arithmetic:     LRC uniform-separation phi(n) residues, Berry-Keating {pi k^2} spectrum.")
    print("   'One programme' = a BRIDGE from a rigid generating structure to chaotic zeros, NOT one shared")
    print("   substrate. The secp thermal lens matches the ZERO side; it does NOT describe the LRC/operator side.")

    print("\n[done]")


if __name__ == '__main__':
    main()
