"""
The phi(n) reach law at scale -- v2, with the controls that decide it.

v1 found: spine reach is flat within a phi-class and ordered by phi.
v2 asks the two questions that could make that finding empty.

  CONTROL A (does coprimality matter?)  phi(n) points drawn from ALL of
      {1..n-1}/n, coprime or not.  If A matches the spine, "spine" is doing
      no work and the finding is just "phi(n) shots".

  CONTROL B (does the grid matter?)  phi(n) points drawn from the continuum
      of the window.  If B matches the spine, the rational structure is doing
      no work either.

  CONTROL C (are the shots independent?)  from the single-shot rate q at
      u = 1/n and the observed reach R, the effective number of independent
      shots is  k_eff = log(1-R)/log(1-q).  Independent shots would give
      k_eff = phi(n).

Criterion, boundary discipline and the no-pinned-runner rule: see v1 header.
For a continuum point u = c/D the clear test for reading a/b is
      b*D <= (a*c) mod (b*D*n) * 1 ... -- done exactly via Fraction-free
      integer form: r = (a*c) mod (b*D), clear iff  b*D <= n*r <= n*b*D - b*D.
"""
import random, sys
from math import gcd, log
from collections import defaultdict

def phi(n):
    r, m, p = n, n, 2
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
    d = sorted(abs(v[j] - v[i]) for j in range(n) if j != i)
    dmin = d[0]
    out = []
    for x in d[1:]:
        g = gcd(x, dmin)
        out.append((x // g, dmin // g))
    return out

def clear_at_frac(rs, c, D, n):
    """Clear at u = c/D.  Reading a/b is in the way iff ||a*c/(b*D)|| < 1/n.
    With r = (a*c) mod (b*D): clear iff  b*D <= n*r  and  n*r <= n*b*D - b*D."""
    for a, b in rs:
        m = b * D
        r = (a * c) % m
        if not (m <= n * r and n * r + m <= n * m):
            return False
    return True

def sample_profile(n, cap, rng):
    v = rng.sample(range(1, cap + 1), n)
    g = 0
    for x in v:
        g = gcd(g, x)
    return sorted(x // g for x in v)

DEN = 2520          # continuum-control denominator; window is (0, (n-1)/n)

def run(n, cap, M, seed):
    rng = random.Random(seed)
    sp = spine_points(n)
    k = len(sp)
    all_pts = list(range(1, n))
    tot = hit = ctrlA = ctrlB = q1 = 0
    per_profile = []                      # profile-level means, for a clustered SE
    for _ in range(M):
        v = sample_profile(n, cap, rng)
        prof_hit = 0
        for i in range(n):
            rs = readings(v, i, n)
            tot += 1
            if any(clear_at_frac(rs, p, n, n) for p in sp):
                hit += 1
                prof_hit += 1
            if clear_at_frac(rs, 1, n, n):
                q1 += 1
            pa = rng.sample(all_pts, k)
            if any(clear_at_frac(rs, p, n, n) for p in pa):
                ctrlA += 1
            lo = -(-DEN // n)                 # ceil(DEN/n): the window starts at 1/n
            hi = (n - 1) * DEN // n
            pb = [rng.randint(lo, hi) for _ in range(k)]
            if any(clear_at_frac(rs, c, DEN, n) for c in pb):
                ctrlB += 1
        per_profile.append(prof_hit / n)
    mu = sum(per_profile) / len(per_profile)
    var = sum((x - mu) ** 2 for x in per_profile) / (len(per_profile) - 1)
    se = (var / len(per_profile)) ** 0.5   # clustered on the profile
    return tot, hit, ctrlA, ctrlB, q1, se

def keff(R, q):
    if R >= 1 or q <= 0 or q >= 1:
        return float('nan')
    return log(1 - R) / log(1 - q)

def selfcheck():
    """The AP (1,...,8): runner 1's reading INSIDE ITS WINDOW [1/8, 7/8] must be
    exactly the four points 1/8, 3/8, 5/8, 7/8 -- MANUSCRIPT section 1.2.
    The window's lower end is the s = 1 reading; u below 1/n is not a candidate
    at all, and an earlier version of this script wrongly searched there."""
    v, n = list(range(1, 9)), 8
    rs = readings(v, 0, n)
    assert rs == [(2,1),(3,1),(4,1),(5,1),(6,1),(7,1)], rs
    lo, hi = DEN // 8, 7 * DEN // 8        # the window [1/8, 7/8]
    got = [c for c in range(lo, hi + 1) if clear_at_frac(rs, c, DEN, n)]
    want = [DEN//8, 3*DEN//8, 5*DEN//8, 7*DEN//8]
    assert got == want, (got[:20], want)
    print(f"self-check: AP (1..8), runner 1 -- reading is exactly "
          f"{{1/8, 3/8, 5/8, 7/8}}, six readings {[a for a,_ in rs]}   PASS")

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    selfcheck()
    print()
    NS = [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24]
    for mult in (10, 50):
        print(f"=== speeds drawn from [1, {mult}n], M = {M} profiles per n ===")
        print(f"{'n':>3} {'phi':>4} {'inst':>7} {'spine':>7} {'se':>7} {'ctrlA':>7} "
              f"{'ctrlB':>7} {'q(1/n)':>7} {'k_eff':>6}")
        print("-" * 68)
        rows = defaultdict(list)
        for n in NS:
            tot, hit, cA, cB, q1, se = run(n, mult * n, M, seed=7919 * n + mult)
            R, q = hit / tot, q1 / tot
            rows[phi(n)].append((n, R, se))
            print(f"{n:>3} {phi(n):>4} {tot:>7} {R:>7.4f} {se:>7.4f} {cA/tot:>7.4f} "
                  f"{cB/tot:>7.4f} {q:>7.4f} {keff(R, q):>6.2f}")
        print()
        print("  phi-class flatness (phi-law: flat; n-law: falling)")
        for ph in sorted(rows):
            if len(rows[ph]) < 2:
                continue
            vals = [R for _, R, _ in rows[ph]]
            ses = [s for _, _, s in rows[ph]]
            spread = max(vals) - min(vals)
            print(f"    phi={ph:>3}  spread {spread:.4f} ({spread/max(ses):.1f} se)   "
                  + " ".join(f"n={n}:{R:.4f}" for n, R, _ in rows[ph]))
        print()
