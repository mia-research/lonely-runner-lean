"""
Is MANUSCRIPT_v7 section 7.4 true?

7.4 claims every runner is cleared by one of two families:
  A  an own-difference opening   t = a/(8d),  d in D, a = 1 mod 8, d <= a*m <= 7d
  B  a cascade lattice           t = p/(8D),  p in {1,3,5,7}, D <= 7*d_min

7.4 implies LRC(8) (section 7.3) but is STRICTLY STRONGER: it constrains WHERE the moment
is, while LRC asks only that one exist. So 7.4 could be false with LRC(8) still true --
section 1.3 says as much, calling the first-window form "a choice, not the target".

A single runner failing BOTH families settles it, and tells the owner whether the framework
must relax to later laps. Random sampling will not find one: family A failures are
constructible but vanishingly rare under draws (0 in 200,000 inside the only band where they
can occur). This anneals on both families at once.

Scale-free: fix d_min = m and search the other six differences. Exact integers throughout.
"""
import random, sys

def countA(ds):
    m = min(ds); n = 0
    for d in sorted(set(ds)):
        a = 1
        while a * m <= 7 * d:
            if a * m >= d and all(d <= (a * e) % (8 * d) <= 7 * d for e in ds):
                n += 1
            a += 8
    return n

def countB(ds):
    m = min(ds); n = 0
    for D in range(1, 7 * m + 1):
        for p in (1, 3, 5, 7):
            if all(D <= (e * p) % (8 * D) <= 7 * D for e in ds):
                n += 1
    return n

def score(ds):
    """Drive family A to zero first -- it is the rare one -- then family B."""
    a = countA(ds)
    if a > 0:
        return (1, a)
    return (0, countB(ds))

def anneal(m, rng, iters, restarts):
    best = None
    hi = 8 * m - 1
    for _ in range(restarts):
        ds = [m] + [rng.randint(m + 1, hi) for _ in range(6)]
        cur = score(ds)
        for t in range(iters):
            j = rng.randrange(1, 7)
            old = ds[j]
            ds[j] = (rng.randint(m + 1, hi) if rng.random() < 0.3
                     else max(m + 1, min(hi, old + rng.choice([-3, -2, -1, 1, 2, 3]))))
            new = score(ds)
            if new <= cur:
                cur = new
            else:
                ds[j] = old
            if best is None or cur < best[0]:
                best = (cur, sorted(ds))
            if cur == (0, 0):
                return best
    return best

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 20260914)
    print("annealing for a runner failing BOTH families  (target score (0,0))\n")
    print(f"{'d_min':>7} {'best score':>12} {'meaning':>34}")
    print("-" * 58)
    for m in (30, 120, 500, 1974):
        (s, ds) = anneal(m, rng, iters=4000, restarts=60)
        mean = ("family A cleared %d times" % s[1] if s[0] == 1
                else ("BOTH FAIL -- counterexample" if s[1] == 0
                      else "A fails; B cleared %d times" % s[1]))
        print(f"{m:>7} {str(s):>12} {mean:>34}")
        if s[0] == 0:
            print(f"         differences: {ds}")
