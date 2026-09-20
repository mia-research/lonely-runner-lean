"""
Adversarial hunt with NOTHING restricted.

The gap is a scale D = k*d_min, the numerator a runs over the odds, there is no window, no
restriction to p in {1,3,5,7}, no a = 1 mod 8, no bound on the lap.  This is the construction
as the owner states it.

Question: how large can the gap index k be forced?  If a determined search cannot push it
far, that is evidence the construction reaches every runner quickly.  If it can be pushed
without limit, that is a real issue rather than a framing error.

Scale-free: fix d_min = 1 and search the other six readings as rationals.
"""
import random, sys
from fractions import Fraction as F

def cd(x):
    fr = x - int(x)
    if fr < 0:
        fr += 1
    return min(fr, 1 - fr)

def first_k(S, kmax=300):
    """S = the six readings (d_min = 1 is implicit and always clears at a/(8k) forms)."""
    for k in range(1, kmax + 1):
        for a in range(1, 8 * k + 9, 2):
            t = F(a, 8 * k)
            if cd(t) >= F(1, 8) and all(cd(s * t) >= F(1, 8) for s in S):
                return k
    return None

def anneal(rng, den, hi, iters, restarts):
    best = (0, None)
    for _ in range(restarts):
        S = [F(rng.randint(den, den * hi), den) for _ in range(6)]
        cur = first_k(S) or 0
        for _ in range(iters):
            j = rng.randrange(6)
            old = S[j]
            S[j] = (F(rng.randint(den, den * hi), den) if rng.random() < 0.35
                    else old + F(rng.choice([-3, -2, -1, 1, 2, 3]), den))
            if S[j] < 1:
                S[j] = old
                continue
            new = first_k(S) or 0
            if new >= cur:
                cur = new
            else:
                S[j] = old
            if cur > best[0]:
                best = (cur, sorted(S))
    return best

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5150)
    print("maximising the gap index k, nothing restricted\n")
    print(f"{'reading denominator':>20} {'largest k forced':>18}")
    print("-" * 40)
    for den in (1, 2, 3, 4, 6, 8, 12):
        k, S = anneal(rng, den, 40, iters=700, restarts=14)
        print(f"{den:>20} {k:>18}")
        if S:
            print(f"     at readings {[str(x) for x in S]}")
