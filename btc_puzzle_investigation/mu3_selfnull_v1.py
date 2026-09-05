#!/usr/bin/env python3
"""
mu3_selfnull_v1.py -- decisive diagnostic for PREREG_mu3_orthogonal_projection_v1.md.

The D4 = S_y - S_g contrast is confounded: the two readouts' NULL-A ensembles use different orbit
sizes ((n-1)/6 for the mu3-invariant y, (n-1)/2 for the non-invariant g).  This script removes the
confound by measuring EACH readout against ITS OWN symmetry-matched null:

    rho_f = S_f(real) / mean S_f(NULL-A)     (top-16 tail suppression ratio)

If rho < 1 for the mu3-INVARIANT readouts (y, x, xy) and rho ~ 1 for the non-invariant ones
(g, x-x0, y(x-x0)), the suppression tracks mu3-invariance -> H_proj, cleanly, per row.
If rho < 1 for y but ~ 1 for x, the effect is specific to y, not to invariance.

Reuses the verified machinery of mu3_projection_v1.py.  Usage: mu3_selfnull_v1.py [M]
"""
import sys
import numpy as np
from mu3_projection_v1 import (count_E, is_prime, cube_root_unity, order3_modn, find_generator,
                               coords, mu6_reps, readout, Q_at, S_top, orbit_partition, null_S,
                               stratum, find_units)

# readout kind, #R, mu3-invariant?
READS = [('x', 2, True), ('x_x0', 2, False),
         ('y', 4, True), ('gx1x2', 4, False),
         ('xy', 6, True), ('y_x_x0', 6, False)]


def run(p, n, M, rng):
    beta = cube_root_unity(p); lam = order3_modn(n); G = find_generator(p, n)
    xs, ys = coords(G, p, n); reps = mu6_reps(n, lam)
    x0 = next(v for v in range(1, p) if (v*v % p*v + 7) % p != 0)
    pairs = ((a, b) for a in range(1, p) for b in range(a + 1, p))
    x1, x2 = next((a, b) for a, b in pairs
                  if (a*a % p*a+7) % p != 0 and (b*b % p*b+7) % p != 0
                  and {a, b} != {beta*a % p, beta*b % p})
    orb6 = orbit_partition(n, lam, mu3=True)
    orb2 = orbit_partition(n, lam, mu3=False)
    out = {}
    for kind, R, inv in READS:
        c = readout(kind, xs, ys, p, x0=x0, x1=x1, x2=x2)
        S, _ = S_top(Q_at(c, reps))
        orbits = orb6 if inv else orb2
        Sn = null_S(c, orbits, reps, M, rng)
        out[kind] = (R, inv, S / p, Sn.mean() / p, S / max(Sn.mean(), 1e-9))
    return p, n, stratum(p), out


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    rng = np.random.default_rng(20260724)
    units = find_units(1000, 12000, 6)
    allu = [pn for s in ('S1', 'S2', 'S3') for pn in units[s]]
    print("=" * 100)
    print("mu3 SELF-NULL suppression rho_f = S_real / S_null  per readout  (M=%d)" % M)
    print("rho<1 for mu3-INVARIANT only => suppression tracks invariance (H_proj)")
    print("=" * 100)
    print("\n p     n     strat | " + " ".join("%-14s" % ("%s(#R%d,%s)" % (k, R, 'I' if inv else '.'))
                                                for k, R, inv in READS))
    agg = {k: [] for k, _, _ in READS}
    for p, n in allu:
        _, _, st, out = run(p, n, M, rng)
        row = " ".join("%5.2f/%4.2f" % (out[k][2], out[k][4]) for k, _, _ in READS)
        print(" %-5d %-5d %-5s | %s" % (p, n, st, row))
        for k, _, _ in READS:
            agg[k].append(out[k][4])
    print("\n=== mean rho_f over %d units (rho = S_real/S_null; <1 = suppressed) ===" % len(allu))
    for k, R, inv in READS:
        arr = np.array(agg[k])
        print("  %-8s #R=%d  %-13s  mean rho = %.3f   (min %.3f max %.3f)"
              % (k, R, 'mu3-INVARIANT' if inv else 'non-invariant', arr.mean(), arr.min(), arr.max()))
    print("SELFNULL_DONE")


if __name__ == '__main__':
    main()
