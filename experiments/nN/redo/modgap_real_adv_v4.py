"""modgap_real_adv_v4 (2026-10-06): the boundary of the arc criterion in rho_min, by continuation.  Start from the exact counterexample of E416 (rho_min = 6) and raise the lower bound r in steps of 1/10 up to 9; at each r clip the previous
solution to rho_i >= r, re-optimise F(rho) = max over u in [1, 6] of min_i (dist_i(u) - 1/7) with coordinate perturbations (floats STEER only; F < 0 means no clear point of the arc), and verify EXACTLY: the six rationals (limit_denominator
10^6, or 10^7 if needed) are run through the exact cascade in u from u = 1; a landing above 6 is an exact counterexample for that r.  Seeded.  Reported: for each r, whether an exact counterexample with all rho_i >= r (exactly: min of the rationals >= r)
was found, its landing as a Fraction and the rationals; the largest r with an exact counterexample."""
import random, math
from fractions import Fraction as F
def F_of(rho, grid=500):
    best = -1.0
    for g in range(grid + 1):
        u = 1 + 5 * g / grid
        m = min(abs(((r * u / 7) + 0.5) % 1.0 - 0.5) for r in rho) - 1 / 7
        if m > best: best = m
    return best
def exact(rho_fracs):
    u = F(1)
    for _ in range(6000):
        blocked = []
        for r in rho_fracs:
            x = r * u / 7
            if abs(x - round(x)) < F(1, 7): blocked.append(F(7 * round(x) + 1) / r)
        if not blocked: return u <= 6, u
        u = max(blocked)
        if u > 6: return False, u
    return None, u
rnd = random.Random(20261006)
start = [F(5), F(1412741, 261840), F(525941, 88195), F(5575838, 821095), F(189353, 24304), F(7946201, 940370)]
out = open('modgap_real_adv_v4.out', 'w'); out.write(__doc__ + "\n")
cur = [float(x) for x in start]; last_ok = None
for step in range(0, 31):
    r = 6 + step / 10
    cur = sorted(max(r, x) for x in cur)
    best = (F_of(cur), cur)
    for attempt in range(8):
        rho = list(best[1]); f = best[0]; sc = 0.5
        for it in range(500):
            i = rnd.randrange(6); cand = list(rho); cand[i] = max(r, cand[i] + rnd.gauss(0, sc))
            cand.sort(); fc = F_of(cand, 300)
            if fc < f: rho, f = cand, fc
            if it % 120 == 119: sc *= 0.5
        if f < best[0]: best = (f, rho)
        if best[0] < -1e-4: break
        # kick
        best = (best[0], sorted(max(r, x + rnd.gauss(0, 0.3)) for x in best[1]))
        best = (F_of(best[1]), best[1])
    cur = list(best[1])
    found = None
    for den in (10 ** 5, 10 ** 6, 10 ** 7):
        cands = [F(x).limit_denominator(den) for x in cur]
        if min(cands) < r: cands = [max(c, F(r).limit_denominator(1000)) for c in cands]
        ok, u = exact(cands)
        if ok is False: found = (cands, u); break
    if found:
        last_ok = r
        out.write("r = %.1f: exact counterexample, min rho = %s, landing u = %s\n   rho = %s\n" % (r, min(found[0]), found[1], [str(c) for c in found[0]]))
    else:
        out.write("r = %.1f: no exact counterexample found (steered F = %.5f)\n" % (r, best[0]))
    out.flush()
out.write("largest r with an exact counterexample found: %s\n" % last_ok)
out.close(); print(open('modgap_real_adv_v4.out').read()[len(__doc__):][:6000])
