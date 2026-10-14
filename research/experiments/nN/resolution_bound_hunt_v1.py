"""
How large can the needed RESOLUTION get?

The framework frames any speed set -- rational or irrational -- as an integer problem at a
chosen resolution D: candidate instants are t = a/(8D) with a = 1 mod 8, and the clearing
test is Proposition 2.1, d <= (a*e mod 8D) <= 7D.

MANUSCRIPT section 7.3: "no bound is offered on how far the procedure's search extends."

Random sampling says the minimal resolution is tiny -- 1 for ~40% of runners, never above 13
over 4,800 runners with speeds to 5,000. If that is a real bound rather than a sampling
artefact, LRC(8) per runner reduces to a FINITE check at bounded resolution, and the
framework supplies the bound. That would be a theorem.

So this anneals to MAXIMISE the minimal resolution. If a determined search cannot push it
far, the bound is worth conjecturing and proving. If it grows without limit, it is not.

Scale-free: the reading vector decides everything, so d_min is fixed and the other six vary.
Exact integers throughout.
"""
import random, sys

def min_resolution(ds, Dmax, amax_mult=400):
    for D in range(1, Dmax + 1):
        a = 1
        while a <= amax_mult * D:
            if all(D <= (a * e) % (8 * D) <= 7 * D for e in ds):
                return D
            a += 8
    return None

def anneal(m, rng, iters, restarts, Dmax=400):
    best = (0, None)
    hi = 40 * m
    for _ in range(restarts):
        ds = [m] + [rng.randint(m + 1, hi) for _ in range(6)]
        cur = min_resolution(ds, Dmax) or Dmax
        for _ in range(iters):
            j = rng.randrange(1, 7)
            old = ds[j]
            ds[j] = (rng.randint(m + 1, hi) if rng.random() < 0.4
                     else max(m + 1, min(hi, old + rng.choice([-5, -2, -1, 1, 2, 5]))))
            new = min_resolution(ds, Dmax) or Dmax
            if new >= cur:
                cur = new
            else:
                ds[j] = old
            if cur > best[0]:
                best = (cur, sorted(ds))
        # keep going from the best found
    return best

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 314159)
    print("annealing to MAXIMISE the minimal resolution\n")
    print(f"{'d_min':>7} {'largest minimal D found':>25}")
    print("-" * 36)
    for m in (1, 7, 30, 211, 1974):
        D, ds = anneal(m, rng, iters=1500, restarts=25)
        print(f"{m:>7} {D:>25}")
        print(f"         at differences {ds}")
