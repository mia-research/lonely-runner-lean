# Refine the hardest arrangements to see what the landing R* converges to (is 12 the supremum?).  Coordinate hill-climb at shrinking scales on the float cascade
# (edge tolerance), starting from the best exact-confirmed arrangements of extremes_deep_v1; report R*, the readings, and rational guesses of the limit.
import sys, random, math
from fractions import Fraction as F
exec(open('extremes_deep_v1.py').read().split('\nif __name__ ==')[0])
starts = [[1.0, 2.3664, 3.149, 4.1961, 5.2243, 5.7986, 7.4506], [1.0, 2.3089, 3.2365, 4.2023, 5.2324, 5.8113, 7.4652],
          [1.0, 2.3594, 3.3086, 4.3152, 5.3594, 5.9672, 7.6655], [1.0, 2.5181, 3.1987, 4.1343, 4.5214, 5.6212, 7.0187]]
def refine(rho, seed, rounds=40):
    rnd = random.Random(seed); cur = fpath(rho)[0]
    for scale in [10 ** (-k / 2) for k in range(2, 17)]:
        for _ in range(4000):
            new = list(rho); i = rnd.randrange(1, 7); new[i] += rnd.gauss(0, scale)
            new = [1.0] + sorted(new[1:])
            if len(set(new)) < 7 or new[-1] > 9.0 or new[1] <= 1.0: continue
            R, n = fpath(new)
            if n >= 10**6: continue
            if R > cur: rho, cur = new, R
    return cur, rho
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
for k, s in enumerate(starts):
    cur, rho = refine(s, 11 + k)
    rh = [F(x).limit_denominator(10**9) for x in rho]; steps, Rend = path(rh)
    print("start %d: R* -> %.10f  (exact %.10f, %d moves)  readings %s" % (k + 1, cur, float(Rend), len(steps), [round(x, 6) for x in rho]), flush=True)
    print("         rational guesses (denominator <= 60):", [str(F(x).limit_denominator(60)) for x in rho])
    print("         last setter (rank, lap):", (steps[-1]['setter'] + 1, steps[-1]['lap']) if steps else None, " path:", " ".join("%d.%d" % (m['setter'] + 1, m['lap']) for m in steps), flush=True)
