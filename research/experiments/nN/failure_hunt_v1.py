"""
A direct hunt for a runner the procedure does NOT return for.

WHY THIS IS NOT TIED TO INTEGER SPEEDS.
The procedure's verdict for runner i depends only on its own reading vector
s = (s_1, ..., s_{n-2}), the non-minimal differences divided by d_min. Any multiset of
positive reals is realisable as one runner's differences -- put the subject at 0 and the
others at those offsets -- so searching over reading vectors searches the per-runner problem
in full generality. No bound on speeds, no integrality, no exhaustive family.

WHAT A HIT WOULD MEAN.
The procedure returns iff the open zones leave some point of the closed window
[1/n, (n-1)/n] clear. A reading vector leaving nothing clear REFUTES part 7 -- the claim
that the procedure always returns. It would NOT refute LRC at that n: the window is the
first lap of the nearest runner, and loneliness later is untouched by it. The two claims
are different and only the first is at stake here.

WHAT THE SLACK LOOKS LIKE.
A reading of any size covers a fraction 2/n of the window (zones of width 2/(ns) spaced
1/s apart), so n-2 readings can cover at most 2(n-2)/n of it -- 1.5 at n = 8. There is room
by size alone. Section 6.1 already says size cannot decide it, so the question is whether
the zone patterns can be brought into phase, and that is what is searched here.

EXACTNESS. Fractions with bounded denominator throughout; open zones; never merged. A
reported hit is an exact object and is re-verified independently before being believed.
"""
import sys, random
from fractions import Fraction as F

def clear_points(S, n):
    """Clear components of the window under readings S. Returns list of clear points."""
    lo, hi = F(1, n), F(n - 1, n)
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

def score(S, n):
    """Fewer clear components is tighter. 0 would be a refutation of part 7."""
    return len(clear_points(S, n))

def rand_reading(rng, D, R):
    q = rng.randint(1, D)
    p = rng.randint(q, q * R)          # ensures s >= 1
    return F(p, q)

def anneal(n, rng, D=48, R=40, iters=60000, restarts=40):
    best_global = None
    for _ in range(restarts):
        S = [rand_reading(rng, D, R) for _ in range(n - 2)]
        cur = score(S, n)
        T0 = 3.0
        for t in range(iters // restarts):
            T = max(0.02, T0 * (1 - t / (iters / restarts)))
            j = rng.randrange(len(S))
            old = S[j]
            if rng.random() < 0.5:
                num, den = old.numerator, old.denominator
                num += rng.choice([-2, -1, 1, 2])
                den = max(1, min(D, den + rng.choice([-1, 0, 1])))
                cand = F(max(num, den), den)
            else:
                cand = rand_reading(rng, D, R)
            S[j] = cand
            new = score(S, n)
            if new <= cur or rng.random() < pow(2.718, -(new - cur) / T):
                cur = new
            else:
                S[j] = old
            if best_global is None or cur < best_global[0]:
                best_global = (cur, list(S))
            if cur == 0:
                return best_global
    return best_global

def verify(S, n):
    """Independent re-check of a claimed hit, by a different route: walk the window's
    candidate points and confirm each is strictly inside some zone."""
    lo, hi = F(1, n), F(n - 1, n)
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
    cands = {lo, hi}
    for a, b in Z:
        for x in (a, b):
            if lo <= x <= hi:
                cands.add(x)
    bad = [u for u in sorted(cands) if not any(a < u < b for a, b in Z)]
    return bad

if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20260913
    rng = random.Random(seed)
    print("hunting for a reading vector that leaves NOTHING clear in the window")
    print("arbitrary rational readings >= 1; exact; a hit refutes part 7, not LRC\n")
    print(f"{'n':>3} {'readings':>9} {'best components found':>22}")
    print("-" * 42)
    for n in (5, 6, 7, 8, 9, 10, 11, 12):
        c, S = anneal(n, rng)
        print(f"{n:>3} {n-2:>9} {c:>22}", flush=True)
        print(f"        best vector: {[str(x) for x in S]}", flush=True)
        if c == 0:
            bad = verify(S, n)
            print(f"        *** CANDIDATE REFUTATION *** independent check leaves "
                  f"{len(bad)} clear points", flush=True)
