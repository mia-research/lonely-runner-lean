#!/usr/bin/env python3
"""
coherent_pool_p0prime_stageC_setup_v1.py -- Stage C setup for
PREREG_coherent_pool_P0prime_v1.md: the HELD-OUT stratum S.

(1) Enumerate S = first 12 primes p>547 with p=7 (mod 12), n=#E(F_p) prime,
    6 | n-1  (matches the twist stratum(p%12==7,12,547) and the row-budget
    curve requirement).  These primes have NEVER been run through row-budget.
(2) Compute valid curve params per prime: beta = an order-3 element of F_p^*
    (GLV cube root), lam found from the curve, C-EQ-int == 0 (x_{lam d}=beta x_d).
(3) Generate the frozen frequency list by the mu6 x conj orbit recipe:
    representatives of the order-12 group (b,c) -> (u*b, +-c), u in mu6 c F_p^*,
    generic stratum (b,c != 0).  Subsample m = min(Norb_gen, BUDGET//n) with
    BUDGET = 16_000_000 (so m*n ~ 1.6e7, matching the discovery budget policy),
    by a SEEDED sampling of distinct canonical orbit reps.  Freeze to
    <out> and print its SHA-256 -- recorded BEFORE any pool value.

DISCLOSURE: the original discovery subsample generator is not on disk, so this
subsample RULE is a reconstruction of the recipe (a fixed, seeded, declared
rule), which is prereg-compliant (a NEW frozen list, section 6) but is a
reconstruction, not a byte-match.  The held-out PRIMES are genuinely OOS.

Exact integers only in the curve/orbit path (no float).  check_no_float passes.
"""
import argparse, hashlib
import numpy as np
from sympy import isprime, primitive_root
from row_budget_core_v1 import curve_orbit

BUDGET = 16_000_000


def find_S(count=12, pmin=547):
    """first `count` primes p>pmin, p=7 mod12, n=#E(F_p) prime, 6|n-1."""
    out = []
    p = pmin
    while len(out) < count:
        p += 1
        if not isprime(p) or p % 12 != 7:
            continue
        r = curve_orbit(p)
        if r is None:
            continue
        X, Y, n = r
        if (n - (p + 1)) ** 2 > 4 * p:      # Hasse guard, exact (no sqrt)
            continue
        if not isprime(n) or (n - 1) % 6 != 0:
            continue
        out.append((p, int(n)))
    return out


def curve_params(p, n):
    """Return (beta, lam) with beta order-3 in F_p^*, x_{lam d}=beta x_d exactly,
       or None if neither nontrivial cube root satisfies C-EQ-int=0."""
    X, Y, nn = curve_orbit(p)
    assert nn == n
    g = int(primitive_root(p))
    z3 = pow(g, (p - 1) // 3, p)            # order-3 element (primitive cube root)
    for beta in (z3, pow(z3, 2, p)):
        xb = beta * X[1] % p
        hit = np.nonzero((X == xb) & (Y == Y[1]))[0]
        if hit.size == 0:
            continue
        lam = int(hit[0])
        idx = (lam * np.arange(n)) % n
        ceq = int(np.max((X[idx] - beta * X) % p))
        if ceq == 0:
            return beta, lam
    return None


def mu6_of(p):
    """the six 6th-roots of unity in F_p^* (p = 1 mod 6), as a sorted int list."""
    g = int(primitive_root(p))
    z6 = pow(g, (p - 1) // 6, p)
    s = set()
    x = 1
    for _ in range(6):
        s.add(x); x = x * z6 % p
    assert len(s) == 6, "mu6 not order 6"
    return sorted(s)


def orbit_rep(b, c, mu6, p):
    """canonical (lex-min) representative of the orbit {(u*b, +-c): u in mu6}."""
    best = None
    for u in mu6:
        ub = u * b % p
        for cc in (c % p, (p - c) % p):
            t = (ub, cc)
            if best is None or t < best:
                best = t
    return best


def gen_freqs(p, n, seed):
    """seeded distinct canonical orbit reps, generic stratum (b,c != 0),
       count m = min(Norb_gen, BUDGET//n).  Returns sorted list of (b,c)."""
    Norb_gen = (p - 1) * (p - 1) // 12
    m = min(Norb_gen, BUDGET // n)
    mu6 = mu6_of(p)
    rng = np.random.default_rng(seed)
    reps = set()
    if m >= Norb_gen:                      # truly exhaustive (never for S)
        for b in range(1, p):
            for c in range(1, p):
                reps.add(orbit_rep(b, c, mu6, p))
        return sorted(reps), Norb_gen, m, True
    # subsampled: seeded rejection sampling of distinct canonical orbit reps
    while len(reps) < m:
        b = int(rng.integers(1, p)); c = int(rng.integers(1, p))
        reps.add(orbit_rep(b, c, mu6, p))
    return sorted(reps), Norb_gen, m, False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="coherent_pool_p0prime_stageC_S_FREQS.txt")
    ap.add_argument("--seed", type=int, default=20260825)
    a = ap.parse_args()

    S = find_S()
    print("HELD-OUT stratum S (p=7 mod12, n prime, 6|n-1, p>547):")
    lines = [f"# stratum S for PREREG_coherent_pool_P0prime_v1.md  seed={a.seed} "
             f"BUDGET={BUDGET}"]
    params = {}
    for p, n in S:
        cp = curve_params(p, n)
        assert cp is not None, f"no valid (beta,lam) with C-EQ-int=0 at p={p}"
        beta, lam = cp
        params[p] = (n, beta, lam)
        print(f"  p={p:>5} n={n:>5} beta={beta:>5} lam={lam:>5}  "
              f"C-EQ-int=0  (p mod4={p%4}, p mod3={p%3})")

    print(f"\nGenerating frozen freq list -> {a.out}")
    for p, n in S:
        reps, Norb, m, exhaustive = gen_freqs(p, n, a.seed + p)
        nn, beta, lam = params[p]
        lines.append(f"# p={p} n={n} beta={beta} lam={lam} Norb_gen={Norb} "
                     f"m={len(reps)} exhaustive={int(exhaustive)}")
        for (b, c) in reps:
            lines.append(f"{p} {b} {c}")
        print(f"  p={p:>5} Norb_gen={Norb:>8}  m={len(reps):>6}  "
              f"exhaustive={int(exhaustive)}  (m*n={len(reps)*n})")

    blob = "\n".join(lines) + "\n"
    with open(a.out, "w") as f:
        f.write(blob)
    sha = hashlib.sha256(blob.encode()).hexdigest()
    print(f"\nFROZEN {a.out}")
    print(f"SHA-256: {sha}")
    print("  ^ recorded BEFORE any pool value (prereg section 6 / section 9).")


if __name__ == "__main__":
    main()
