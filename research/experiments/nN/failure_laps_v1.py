"""
Given that part 7 is refuted, how much is needed to repair it?

failure_hunt_v1 found reading vectors leaving NOTHING clear in the window, refuting
the claim that the procedure returns in the first window. This collects a population of
such failures, at several n, and measures how many LAPS are needed before a clear instant
appears -- i.e. what a corrected claim would have to say.

Exact throughout; open zones; never merged.
"""
import sys, random
from fractions import Fraction as F
from collections import Counter

def lap_window(L, n):
    return F(L - 1) + F(1, n), F(L - 1) + F(n - 1, n)

def clear_in_lap(S, n, L):
    lo, hi = lap_window(L, n)
    Z = []
    for s in S:
        k = 0
        while True:
            a = F(n * k - 1, n) / s
            if a > hi:
                break
            b = F(n * k + 1, n) / s
            if b > lo:
                Z.append((a, b))
            k += 1
    Z.sort()
    cands = sorted({lo} | {b for _, b in Z if lo <= b <= hi})
    out, ptr, maxb = [], 0, None
    for u in cands:
        while ptr < len(Z) and Z[ptr][0] < u:
            b = Z[ptr][1]
            if maxb is None or b > maxb:
                maxb = b
            ptr += 1
        if maxb is None or not (maxb > u):
            out.append(u)
    return out

def first_lap_that_works(S, n, maxL=40):
    for L in range(1, maxL + 1):
        c = clear_in_lap(S, n, L)
        if c:
            return L, c[0]
    return None, None

def rand_reading(rng, D, R):
    q = rng.randint(1, D)
    return F(rng.randint(q, q * R), q)

def hunt(n, rng, tries, D=48, R=40, iters=1500):
    hits = []
    for _ in range(tries):
        S = [rand_reading(rng, D, R) for _ in range(n - 2)]
        cur = len(clear_in_lap(S, n, 1))
        for t in range(iters):
            j = rng.randrange(len(S))
            old = S[j]
            S[j] = rand_reading(rng, D, R)
            new = len(clear_in_lap(S, n, 1))
            if new <= cur:
                cur = new
            else:
                S[j] = old
            if cur == 0:
                hits.append(list(S))
                break
    return hits

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 5551212)
    print("failures of the first window, and the lap that recovers them\n")
    print(f"{'n':>3} {'tries':>6} {'failures found':>15} {'lap needed (histogram)':>28}")
    print("-" * 60)
    for n in (5, 6, 7, 8, 9, 10, 11, 12):
        hits = hunt(n, rng, tries=60)
        laps = Counter()
        for S in hits:
            L, _ = first_lap_that_works(S, n)
            laps[L] += 1
        print(f"{n:>3} {60:>6} {len(hits):>15} {str(dict(sorted(laps.items()))):>28}",
              flush=True)
        if hits:
            print(f"        example: {[str(x) for x in hits[0]]}", flush=True)
