#!/usr/bin/env python3
"""glv_norm_readout_matched_null_v2.py -- the surviving lane vs a matched null, screen FIXED.

TWO BUGS IN v1, both caught by its own controls (recorded, not silently fixed):

 (B1) The parity screen used chi_k(-1), which is the wrong quantity for an x-readout.
      The parity that matters is under d -> -d, and [-d]G = (x, -y): the x-coordinate is
      UNCHANGED.  So ANY function of x alone is automatically EVEN in d, whatever chi_k(-1) is.
      v1 therefore mislabelled chi_2(x) "FORCED ZERO" at p = 3 mod 4 -- contradicting the earlier
      pre-screen script, which measured it moving at exactly those primes.  The only binding
      constraint is the mu_3 one: chi_k(beta) = 1.

 (B2) C-FORCED (Sum_d chi2(y)*N must be 0) is forced ONLY when eps = chi_2(-1) = -1, i.e.
      p = 3 mod 4.  v1 applied it at p = 1 mod 4 and it "failed" correctly -- the control was
      mis-specified, not the mathematics.  secp256k1 has p = 3 mod 4, so the forced regime is the
      relevant one; the control is now applied only where it is valid.

SCOPE (in-scope object).  The CONVERSION d -> [d]G = (x,y): does the scalar's Eisenstein/GLV
lattice footprint N(kappa(d)) couple to a character of the resulting point's x-coordinate?
Nothing here depends on how any d was chosen; scalars are the full group at each prime.

DESIGN.  Both N and the readout are constant on mu_6 orbits {+-d, +-ld, +-l^2 d} (size exactly 6).
Statistic S = sum over classes of w(class)*N(class).  Matched null permutes the readout's
class-values among classes -- preserving every forced symmetry, destroying only the coupling.
Exact permutation p-values (integer counts).  Uniformity of p across primes is the real test;
a single small p at one prime is a discovery-sample artifact until it replicates.

No floats.
"""

import sys
import random


def isqrt_int(x):
    lo, hi = 0, x
    while lo < hi:
        mid = (lo + hi + 1)//2
        if mid*mid <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


def is_prime(m):
    if m < 2:
        return False
    for q in range(2, isqrt_int(m) + 1):
        if m % q == 0:
            return False
    return True


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1)//2, p) == 1 else -1)


def curve_seq(p, A, B):
    def add(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        x1, y1 = P
        x2, y2 = Q
        if x1 == x2 and (y1 + y2) % p == 0:
            return None
        if P == Q:
            num, den = (3*x1*x1 + A) % p, (2*y1) % p
        else:
            num, den = (y2 - y1) % p, (x2 - x1) % p
        lm = num * pow(den, p - 2, p) % p
        x3 = (lm*lm - x1 - x2) % p
        return (x3, (lm*(x1 - x3) - y1) % p)
    pts = []
    for x in range(p):
        r = (x*x % p * x + A*x + B) % p
        for y in range(p):
            if y*y % p == r:
                pts.append((x, y))
    n = len(pts) + 1
    for G in pts:
        seq, cur = [None], None
        for _ in range(n):
            cur = add(cur, G)
            seq.append(cur)
        if next((i for i in range(1, len(seq)) if seq[i] is None), None) == n:
            return n, seq[:n]
    return None, None


def find_beta(p):
    for g in range(2, p):
        b = pow(g, (p - 1)//3, p)
        if b != 1 and pow(b, 3, p) == 1:
            return b
    return None


def glv_norm(d, lam, n, span):
    best = None
    for k2 in range(-span, span + 1):
        r = (d - k2*lam) % n
        for k1 in (r, r - n):
            N = k1*k1 - k1*k2 + k2*k2
            if best is None or N < best:
                best = N
    return best


def kth_root_gen(p, k):
    for g in range(2, p):
        g0 = pow(g, (p - 1)//k, p)
        if all(pow(g0, j, p) != 1 for j in range(1, k)):
            return g0
    return None


def char_exp(x, p, k, g0):
    v = pow(x % p, (p - 1)//k, p)
    cur = 1
    for e in range(k):
        if cur == v:
            return e
        cur = cur * g0 % p
    return None


def analyse(p, B, R, rng):
    n, seq = curve_seq(p, 0, B)
    if n is None or n % 2 == 0 or n % 3 != 1:
        return None
    beta = find_beta(p)
    gx, gy = seq[1]
    lam = next((d for d in range(1, n) if seq[d] == (beta*gx % p, gy)), None)
    if lam is None or (lam*lam + lam + 1) % n:
        return None
    span = 1 + isqrt_int(n)
    N = {d: glv_norm(d, lam, n, span) for d in range(1, n)}

    seen, classes = set(), []
    for d in range(1, n):
        if d in seen:
            continue
        orb = set()
        for s in (d, lam*d % n, lam*lam*d % n):
            orb.add(s)
            orb.add((n - s) % n)
        seen |= orb
        classes.append(sorted(orb))
    if any(len(c) != 6 for c in classes):
        return None
    if any(len({N[d] for d in c}) != 1 for c in classes):
        return None
    Ncls = [N[c[0]] for c in classes]
    M = len(classes)
    eps = legendre(p - 1, p)

    res = []
    for k in (2, 3, 6):
        if (p - 1) % k:
            continue
        g0 = kth_root_gen(p, k)
        if g0 is None:
            continue
        # FIXED screen: x-readouts are automatically even in d; only mu_3 binds.
        if char_exp(beta, p, k, g0) != 0:
            res.append((k, "forced-mu3", None, None, M))
            continue
        cv = []
        bad = False
        for c in classes:
            vals = {char_exp(seq[d][0], p, k, g0) for d in c if seq[d][0] % p}
            if len(vals) != 1:
                bad = True
                break
            cv.append(next(iter(vals)))
        if bad:
            res.append((k, "not-class-fn", None, None, M))
            continue
        w = [1 - 2*v for v in cv] if k == 2 else [1 if v == 0 else -1 for v in cv]
        S = sum(w[i]*Ncls[i] for i in range(M))
        ge = 0
        for _ in range(R):
            q = w[:]
            rng.shuffle(q)
            if abs(sum(q[i]*Ncls[i] for i in range(M))) >= abs(S):
                ge += 1
        res.append((k, "ok", S, (ge + 1, R + 1), M))

    # C-FORCED, only where valid (eps = -1)
    cforced = None
    if eps == -1:
        cforced = sum(legendre(seq[d][1], p)*N[d] for d in range(1, n))
    return {"n": n, "eps": eps, "M": M, "res": res, "cforced": cforced,
            "Ncls": Ncls, "classes": classes, "seq": seq, "p": p}


def plant_power(Ncls, M, R, rng, fracs=(1, 2, 3, 5, 10)):
    """power curve: replace frac/10 of the class readout with sign(N - median)."""
    med = sorted(Ncls)[M//2]
    ideal = [1 if Ncls[i] > med else -1 for i in range(M)]
    base = [1 if rng.random() < 0.5 else -1 for _ in range(M)]  # noqa: float
    out = []
    for f in fracs:
        w = base[:]
        for i in range(M*f//10):
            w[i] = ideal[i]
        S = sum(w[i]*Ncls[i] for i in range(M))
        ge = 0
        for _ in range(R):
            q = w[:]
            rng.shuffle(q)
            if abs(sum(q[i]*Ncls[i] for i in range(M))) >= abs(S):
                ge += 1
        out.append((f*10, ge + 1, R + 1))
    return out


if __name__ == "__main__":
    R = 2000
    rng = random.Random(20260801)
    rows = []
    print("=" * 104)
    print("%-6s %-6s %-5s %-5s | %-8s %-9s %-14s | %s"
          % ("p", "n", "eps", "M", "readout", "S", "exact perm p", "C-FORCED chi2(y)xN"))
    print("=" * 104)
    tested = 0
    for p in range(200, 2600):
        if p % 6 != 1 or not is_prime(p):
            continue
        if tested >= 22:
            break
        got = None
        for B in (7, 2, 3, 5, 11, 13):
            a = analyse(p, B, R, rng)
            if a and any(r[1] == "ok" for r in a["res"]):
                got = a
                break
        if not got:
            continue
        tested += 1
        cf = got["cforced"]
        cfs = ("n/a (eps=+1)" if cf is None else
               ("0 OK" if cf == 0 else "*** %d NONZERO ***" % cf))
        for (k, st, S, pv, M) in got["res"]:
            if st != "ok":
                continue
            rows.append((got["p"], k, S, pv[0], pv[1], M))
            print("%-6d %-6d %-5d %-5d | chi_%-4d %-9d %-14s | %s"
                  % (got["p"], got["n"], got["eps"], M, k, S,
                     "%d/%d" % (pv[0], pv[1]), cfs))
    print("-" * 104)
    below05 = sum(1 for r in rows if r[3]*20 <= r[4])
    below01 = sum(1 for r in rows if r[3]*100 <= r[4])
    print("cells: %d | exact perm p <= 0.05 : %d (expected under the null: %d)"
          " | p <= 0.01 : %d (expected: %d)"
          % (len(rows), below05, len(rows)//20, below01, len(rows)//100))
    # power curve on the largest instance
    if rows:
        big = max(rows, key=lambda r: r[5])
        a = None
        for B in (7, 2, 3, 5, 11, 13):
            a = analyse(big[0], B, 200, rng)
            if a:
                break
        if a:
            print("\nC-PLANT power curve at p=%d (M=%d classes), planted fraction -> exact p:"
                  % (big[0], a["M"]))
            for (pct, num, den) in plant_power(a["Ncls"], a["M"], R, rng):
                print("   %3d%% planted : p = %d/%d   %s"
                      % (pct, num, den, "FIRES" if num*20 <= den else "does not fire"))
