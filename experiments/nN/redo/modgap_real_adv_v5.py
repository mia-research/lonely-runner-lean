"""modgap_real_adv_v5 (2026-10-06): the boundary of the arc criterion in rho_min, by continuation with an interval objective (no grid).  K(rho) = [1, 6] minus the open zones ((7j - 1)/rho_i, (7j + 1)/rho_i); the objective G(rho) =
the largest length of a window of K (0 when K is empty or consists of points); the search minimises G (floats STEER only).  Continuation from the exact counterexample of modgap_real_adv_v4 at r = 6.0, raising r in steps of 1/10 to 9;
at each r the best G found is checked EXACTLY: the six rationals (limit_denominator) through the exact cascade from u = 1; a landing above 6 is an exact counterexample.  Seeded."""
import random
from fractions import Fraction as F
def windows(rho):
    iv = []
    for r in rho:
        j = 1
        while (7 * j - 1) / r < 6:
            iv.append(((7 * j - 1) / r, (7 * j + 1) / r)); j += 1
    iv.sort(); cur = 1.0; best = 0.0
    for a, b in iv:
        if a > cur: best = max(best, a - cur)
        cur = max(cur, b)
        if cur >= 6: return best
    return max(best, 6 - cur)
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
start = [6.0, 468130/72439, 434964/61535, 449337/55381, 767383/82448, 823354/82135]
out = open('modgap_real_adv_v5.out', 'w'); out.write(__doc__ + "\n")
cur = list(start); last = None
for step in range(0, 31):
    r = 6 + step / 10
    cur = sorted(max(r, x) for x in cur); best = (windows(cur), cur)
    for attempt in range(40):
        rho = list(best[1]); g = best[0]; sc = 0.4
        for it in range(1500):
            i = rnd.randrange(6); cand = list(rho); cand[i] = max(r, cand[i] + rnd.gauss(0, sc)); cand.sort(); gc = windows(cand)
            if gc <= g: rho, g = cand, gc
            if it % 300 == 299: sc *= 0.5
            if g == 0.0: break
        if g < best[0]: best = (g, rho)
        if best[0] == 0.0: break
        best = (best[0], sorted(max(r, x + rnd.gauss(0, 0.5)) for x in best[1])); best = (windows(best[1]), best[1])
    cur = list(best[1]); found = None
    for den in (10 ** 5, 10 ** 6, 10 ** 7, 10 ** 8):
        cands = [max(F(x).limit_denominator(den), F(r).limit_denominator(100)) for x in cur]
        ok, u = exact(cands)
        if ok is False: found = (cands, u); break
    if found:
        last = r; out.write("r = %.1f: EXACT counterexample, min rho = %s, landing u = %s\n   rho = %s\n" % (r, min(found[0]), found[1], [str(c) for c in found[0]]))
    else:
        out.write("r = %.1f: none found (least window length reached %.5f)\n" % (r, best[0]))
    out.flush()
out.write("largest r with an exact counterexample: %s\n" % last); out.close(); print(open('modgap_real_adv_v5.out').read()[len(__doc__):][:5500])
