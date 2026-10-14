"""
The phi(n) reach law at scale.

CLAIM UNDER TEST
  The framework's spine reach -- the fraction of runner-instances settled by the
  n spine instants u = p/n, gcd(p,n)=1 -- tracks phi(n), not n.

WHY IT IS TESTABLE
  phi is not monotone in n, so the law has a rival with an opposite prediction:
    phi-law : within a phi-class the rate is flat across n
    n-law   : the rate falls with n (more runners, more readings, harder)
  They disagree sharply on the phi-class {15, 16, 20, 24}, which spans n by 9.

THE OBJECT
  n runners at distinct positive integer speeds, gcd 1. NO runner is pinned at 0.
  For runner i: d_j = |v_j - v_i| over the other n-1; d_min = min d_j; the
  readings are s_j = d_j/d_min for the n-2 that are not the nearest.  (The
  nearest has s = 1 and is clear at every spine point, since ||p/n|| >= 1/n
  whenever gcd(p,n) = 1.)

THE CRITERION
  Reading s = a/b in lowest terms is CLEAR at u = p/n iff ||s*p/n|| >= 1/n.
  With r = (a*p) mod (b*n) this is exactly

      b <= r <= b*(n-1)

  integer arithmetic throughout, no floats anywhere.  This is the criterion
  formalised as ConstructionN.coord_iff.

BOUNDARY DISCIPLINE
  The in-the-way zone is OPEN, so its endpoints are clear: the comparisons above
  are non-strict on purpose.  r = b and r = b*(n-1) are clear, not blocked.
"""
import random, sys
from math import gcd
from collections import defaultdict

def phi(n):
    r, m = n, n
    p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            r -= r // p
        p += 1
    if m > 1:
        r -= r // m
    return r

def spine_points(n):
    return [p for p in range(1, n) if gcd(p, n) == 1]

def readings(v, i, n):
    """Exact readings (a, b) for runner i, as reduced fractions a/b."""
    d = sorted(abs(v[j] - v[i]) for j in range(n) if j != i)
    dmin = d[0]
    out = []
    for x in d[1:]:                      # drop ONE copy of the minimum
        g = gcd(x, dmin)
        out.append((x // g, dmin // g))
    return out

def clear_at(rs, p, n):
    """True iff every reading is clear at u = p/n."""
    for a, b in rs:
        r = (a * p) % (b * n)
        if not (b <= r <= b * (n - 1)):
            return False
    return True

def settled(rs, pts, n):
    return any(clear_at(rs, p, n) for p in pts)

def sample_profile(n, cap, rng):
    v = rng.sample(range(1, cap + 1), n)
    g = 0
    for x in v:
        g = gcd(g, x)
    return sorted(x // g for x in v)

def run(n, cap, M, seed):
    rng = random.Random(seed)
    pts = spine_points(n)
    tot = hit = 0
    first_only = 0                       # settled by u = 1/n alone
    for _ in range(M):
        v = sample_profile(n, cap, rng)
        for i in range(n):
            rs = readings(v, i, n)
            tot += 1
            if settled(rs, pts, n):
                hit += 1
            if clear_at(rs, 1, n):
                first_only += 1
    return tot, hit, first_only

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    NS = [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24]
    print(f"M = {M} profiles per (n, span);  exact integer arithmetic;  no runner pinned at 0")
    print()
    print(f"{'n':>3} {'phi':>4} {'span':>7} {'instances':>10} {'spine reach':>12} {'u=1/n alone':>12}")
    print("-" * 56)
    rows = defaultdict(list)
    for n in NS:
        for mult, tag in ((10, "10n"), (50, "50n")):
            tot, hit, f1 = run(n, mult * n, M, seed=1000 * n + mult)
            rate = hit / tot
            rows[phi(n)].append((n, tag, rate))
            print(f"{n:>3} {phi(n):>4} {tag:>7} {tot:>10} {rate:>11.4f} {f1/tot:>11.4f}")
    print()
    print("phi-classes -- the phi-law predicts a flat column, the n-law a falling one")
    print("-" * 56)
    for ph in sorted(rows):
        by_n = defaultdict(list)
        for n, tag, rate in rows[ph]:
            by_n[n].append(rate)
        if len(by_n) < 2:
            continue
        cells = " ".join(f"n={n}:{sum(v)/len(v):.4f}" for n, v in sorted(by_n.items()))
        vals = [sum(v) / len(v) for v in by_n.values()]
        print(f"  phi={ph:>3}  spread {max(vals)-min(vals):.4f}   {cells}")
