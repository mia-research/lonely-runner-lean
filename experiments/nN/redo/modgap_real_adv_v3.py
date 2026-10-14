"""modgap_real_adv_v3 (2026-10-06): where do exact counterexamples to the arc criterion stop in rho_min?  For rho_min in {5, 6, 7, 8, 9, 10, 12, 14, 16, 20}, rho_i in [rho_min, rho_min + 8]: 300 seeded restarts of the steered
(float) search minimising F(rho) = max_u min_i (dist_i(u) - 1/7) over the arc u in [1, 6]; the best candidates (the 5 least F) are re-verified EXACTLY (Fractions, limit_denominator 10^6, the exact cascade from u = 1; a landing
above 6 is an exact counterexample).  Reported: the least F, whether an exact counterexample was found, and its landing.  The float step only steers; an exact counterexample is the only claim made.  Parallel over rho_min."""
import random, math, sys, time
from fractions import Fraction as F
from multiprocessing import Pool
def F_of(rho, grid=400):
    best = -1.0
    for g in range(grid + 1):
        u = 1 + 5 * g / grid
        m = min(abs(((r * u / 7) + 0.5) % 1.0 - 0.5) for r in rho) - 1 / 7
        if m > best: best = m
    return best
def exact(rho_fracs):
    u = F(1)
    for _ in range(4000):
        blocked = []
        for r in rho_fracs:
            x = r * u / 7
            if abs(x - round(x)) < F(1, 7): blocked.append(F(7 * round(x) + 1) / r)
        if not blocked: return u <= 6, u
        u = max(blocked)
        if u > 6: return False, u
    return None, u
def run(rmin):
    rnd = random.Random(20261006 + rmin); rmax = rmin + 8; pool = []
    for restart in range(300):
        rho = sorted(rnd.uniform(rmin, rmax) for _ in range(6)); f = F_of(rho)
        step = 1.0
        for it in range(300):
            i = rnd.randrange(6); cand = list(rho); cand[i] = min(rmax, max(rmin, cand[i] + rnd.gauss(0, step)))
            cand.sort(); fc = F_of(cand)
            if fc < f: rho, f = cand, fc
            if it % 70 == 69: step *= 0.5
        pool.append((f, rho))
    pool.sort(key=lambda x: x[0]); found = None
    for f, rho in pool[:5]:
        cands = [F(x).limit_denominator(10 ** 6) for x in rho]
        ok, u = exact(cands)
        if ok is False and found is None: found = (f, [str(c) for c in cands], u)
    return rmin, pool[0][0], found
if __name__ == '__main__':
    t0 = time.time(); out = open('modgap_real_adv_v3.out', 'w'); out.write(__doc__ + "\n")
    with Pool(4) as p: res = sorted(p.map(run, (5, 6, 7, 8, 9, 10, 12, 14, 16, 20)))
    for rmin, f, found in res:
        out.write("rho_min = %2d: least steered F = %.5f; exact counterexample: %s\n" % (rmin, f, ("YES, landing u = %s; rho = %s" % (found[2], found[1])) if found else "none among the 5 best"))
    out.write("elapsed %ds\n" % (time.time() - t0)); out.close(); print(open('modgap_real_adv_v3.out').read()[len(__doc__):])
