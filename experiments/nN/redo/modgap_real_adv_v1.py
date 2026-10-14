"""modgap_real_adv_v1 (2026-10-06): is the threshold statement a statement about REAL ratios?  Claim R(5): for six real numbers 5 <= rho_2 <= ... <= rho_7 there is u in [1, 6] with rho_i u mod 7 in [1, 6] for all i
(equivalently the six readings, as ratios to d_min, have a lonely instant at 1/7 in the first clear arc of d_min).  Adversarial search: minimise F(rho) = max over u in [1, 6] of min_i (dist_i(u) - 1/7), where dist_i(u) = distance of
rho_i u / 7 to the nearest integer; F < 0 means NO lonely point (a counterexample to R(5)).  Floats (numpy-free, pure Python) STEER the search only; the best candidates are re-verified exactly by Fractions (the
cascade of the six started at u = 1, exact).  Seeded random restarts (20261006), coordinate perturbations at several scales, rho_i in [5, RHO_MAX].  Also R(rho_2 >= r) for r = 3, 4, 4.5, 5.5 to show where the first
counterexample appears as the lower bound is lowered."""
import random, math, sys
from fractions import Fraction as F
def F_of(rho, grid=4000):
    best = -1.0
    for g in range(grid + 1):
        u = 1 + 5 * g / grid
        m = min(abs(((r * u / 7) + 0.5) % 1.0 - 0.5) for r in rho) - 1 / 7
        if m > best: best = m
    return best
def exact_lonely_in_arc(rho_fracs):
    # exact cascade in u coordinates: start u = 1; zones ((7j-1)/rho, (7j+1)/rho)
    u = F(1)
    for _ in range(2000):
        blocked = []
        for r in rho_fracs:
            x = r * u / 7
            d = abs(x - round(x))
            if d < F(1, 7): blocked.append((F(7 * round(x) + 1) / r))
        if not blocked: return u <= 6, u
        u = max(blocked)
        if u > 6: return False, u
    return None, u
rnd = random.Random(20261006)
out = open('modgap_real_adv_v1.out', 'w'); out.write(__doc__ + "\n")
for rmin, rmax in ((5, 40), (5, 12), (4.5, 40), (4, 40), (3, 40), (5.5, 40)):
    best = (9.0, None)
    for restart in range(120):
        rho = sorted(rnd.uniform(rmin, rmax) for _ in range(6)); f = F_of(rho, 400)
        step = 1.0
        for it in range(260):
            i = rnd.randrange(6); cand = list(rho); cand[i] = min(rmax, max(rmin, cand[i] + rnd.gauss(0, step)))
            cand.sort(); fc = F_of(cand, 400)
            if fc < f: rho, f = cand, fc
            if it % 60 == 59: step *= 0.5
        if f < best[0]: best = (f, rho)
    fv = F_of(best[1], 6000)
    cands = [F(x).limit_denominator(10 ** 6) for x in best[1]]
    ok, u = exact_lonely_in_arc(cands)
    out.write("rho in [%s, %s]: least F found %.5f (refined %.5f); exact check of that rational point (denominators <= 10^6): lonely point in the arc: %s (cascade reaches u = %s)\n" % (rmin, rmax, best[0], fv, ok, float(u)))
out.close(); print(open('modgap_real_adv_v1.out').read()[len(__doc__):])
