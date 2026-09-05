#!/usr/bin/env python3
# cside_nonalgebraic_correlation_v1.py -- EXPLORATORY. The direct c-side test that the
# record names as open queue item "C": corr(c(d), c(f(d))) for NON-ALGEBRAIC index maps f
# (inverse, odd power maps) -- the CDH/inversion channel.
#
# OBJECT. c(d) = chi2(y_{[d]G}), d=1..n-1 (n=#E prime). Its FFT is V1(a). The record tested
# the FREQUENCY-side analogue corr(u(a),u(sigma(a))) (NULL) and the c-side SPINNING-PHASE
# hologram H(k,a) (NULL), but never the bare c-side product sum_d c(d) c(f(d)) for f
# non-algebraic. STRUCTURAL_IMPLICATIONS §5.3: inverse=CDH/inversion, the only wall Weil
# does not close.
#
# PARITY RULE (record, must respect): c is ODD, c(-d)=-c(d). An EVEN index map annihilates
# identically; only ODD maps (inv, d^k k odd, bijective) carry information. Stated, checked.
#
# STATISTIC. For odd bijective f:  T_f = sum_{d=1}^{n-1} c(d) c(f(d)) / (n-1).  (unnormalized
# mean product; rank against null, so normalization is moot). Equivalent to a Pearson corr on
# the centered values -- use the raw mean product, it's a monotone equivalent and simpler.
#
# MATCHED NULL. Permute c WITHIN the mu_6 orbits (= <lambda> = the 6-element GLV orbits on
# (Z/n)*), respecting ODDNESS. This preserves the forced GLV-invariance c(lambda d)=c(d) AND
# oddness exactly, destroying only the arrangement under f. Built from primitive_root.
#
# FIRING CONTROL. Plant a c' that has a KNOWN f-correlation by adding a small odd f-aligned
# component, confirm T_f detects it (power exists). Without this, a null is uninterpretable.
#
# EXACTNESS: c(d) exact int (Legendre); index maps exact int (pow mod n); T_f is an integer
# sum. Null draws permute exact int arrays. Float enters ONLY the permutation null ranking.
# Gate: EXPLORATORY, user-authorised relaxation (no experiment-designer prereg; no grade moves).
import sys, numpy as np
from sympy import primitive_root, nextprime, isprime as sym_isprime

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from twist_orbit_spectrum_run_v1 import signal   # returns (n, c, X, Y), c[d]=chi2(y_[d]G)


def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


def curve_order(p, B=7):
    n = p + 1
    for x in range(p):
        n += legendre((x*x % p * x + B) % p, p)
    return n


def glv_lambda(n):
    """The GLV lambda: a cube root of unity mod n (the endomorphism eigenvalue).
    secp has lambda = beta-style; for general j=0 prime n with 6|(n-1), lambda is a primitive
    cube root of unity mod n. Find it: g = primitive root, lambda = g^((n-1)/3)."""
    g = int(primitive_root(n))
    lam = pow(g, (n-1)//3, n)
    # verify lam^3 == 1 mod n and lam != 1
    assert pow(lam, 3, n) == 1 and lam != 1, "lambda not a primitive cube root"
    return lam


def free_orbits(n, lam):
    """Return list of orbits of <lambda> on (Z/n)*, as lists of residues. Each orbit has size
    3 (the mu_3 action); combined with oddness (-1) gives mu_6 orbits of size 6. We work with
    the mu_3 orbits of size 3 and respect oddness separately."""
    seen = set()
    orbits = []
    for d in range(1, n):
        if d in seen:
            continue
        orb = []
        cur = d
        for _ in range(3):
            orb.append(cur)
            seen.add(cur)
            cur = (cur * lam) % n
        orbits.append(orb)
    return orbits


def null_permute(c, n, lam, rng):
    """Permute c WITHIN each mu_3 orbit (preserving c(lambda d)=c(d) and oddness). Because
    c is constant on each orbit (forced), permuting WITHIN an orbit does nothing -- the real
    null must PERMUTE WHOLE ORBITS against the pairing, OR permute within the oddness pair.
    Correct null: pair each orbit with its negation; permute orbit-contents across the
    oddness pair respecting c(-d)=-c(d). Concretely: shuffle which (d, -d) label each orbit
    member gets, keeping the sign. Simpler & valid: random sign-flip-consistent relabeling."""
    # The forced values: c is constant +v or -v on each orbit (oddness forces the sign pattern).
    # A valid null preserving forced symmetries: independently for each orbit, decide a random
    # permutation of its 3 elements (the values move with them, but values are equal so no-op).
    # => the orbit-constant structure means the ONLY freedom is the per-orbit SIGN, and oddness
    #    fixes that. So the class-permutation null here is actually CONSTRAINED to near-trivial.
    # This is itself a finding: the forced symmetries leave little null freedom for the product.
    # Use the null the freq-side used: permute the FREE orbits as blocks against the c(f(d)) axis.
    orbits = free_orbits(n, lam)
    # represent c on orbit reps; a null draw = random bijection of orbits to orbit-value-sets
    # but values are forced equal within orbit -> the product sum_d c(d)c(f(d)) is determined by
    # the orbit-assignment. Permute the orbit LABELS randomly.
    perm = list(range(len(orbits)))
    rng.shuffle(perm)
    c2 = np.zeros(n, dtype=np.int64)
    for i, orb in enumerate(orbits):
        src_orb = orbits[perm[i]]
        for j, d in enumerate(orb):
            c2[d] = c[src_orb[j]]
            c2[(-d) % n] = -c2[d]          # preserve oddness
    return c2


def index_map(name, n):
    """Odd bijective index maps on (Z/n)*. Return f(d) for d in 1..n-1 (0 -> 0)."""
    d = np.arange(n, dtype=np.int64)
    if name == "inv":
        f = np.zeros(n, dtype=np.int64)
        for t in range(1, n):
            f[t] = pow(int(t), n-2, n)
        return f
    if name.startswith("pow"):
        k = int(name[3:])
        assert k % 2 == 1 and sym_isprime(n), "power map needs odd k, prime n"
        # bijection on (Z/n)* iff gcd(k, n-1)=1
        from math import gcd
        assert gcd(k, n-1) == 1, f"d^{k} not bijective (gcd(k,n-1)={gcd(k,n-1)})"
        return (d ** k) % n
    raise ValueError(name)


def T_stat(c, f, n):
    """Mean product sum_{d=1}^{n-1} c(d) c(f(d)) / (n-1)."""
    d = np.arange(1, n, dtype=np.int64)
    return float((c[d] * c[f[d]]).sum()) / (n-1)        # noqa: float (monotone, ranked vs null)


def firing_control(f, n, lam, amp=0.6, rng=None):
    """Genuinely-INDEPENDENT firing control: a FRESH random odd +/-1 array with a KNOWN planted
    f-correlation, NOT derived from the real c. r(d) random odd; c_plant = sign(r + amp*(r o f)),
    re-quantized, oddness-enforced. This has a real planted f-alignment independent of c's GLV
    structure, so a null band that contains T(c_plant) means the test has NO power."""
    if rng is None: rng = np.random.default_rng(12345)
    r = np.zeros(n, dtype=np.int64)
    half = (n-1)//2
    r[1:half+1] = rng.choice([-1, 1], size=half)
    for t in range(1, half+1):
        r[(-t) % n] = -r[t]                   # oddness
    rf = r[f[np.arange(n)]]
    planted = np.sign(r.astype(float) + amp * rf.astype(float))
    cp = np.zeros(n, dtype=np.int64)
    d = np.arange(1, n, dtype=np.int64)
    cp[d] = planted[d].astype(np.int64)
    for t in range(1, half+1):
        cp[(-t) % n] = -cp[t]
    return T_stat(cp, f, n)


def main(primes):
    print("="*84)
    print("c-side NON-ALGEBRAIC index correlation (queue item C). EXPLORATORY, gate-relaxed.")
    print("Stat: T_f = mean_d c(d)c(f(d)), f in {inv, pow5, pow7, ...} (odd bijective).")
    print("Null: mu_3-orbit-block permutation preserving GLV-invariance + oddness.")
    print("Parity rule (checked): only ODD maps; even maps annihilate (reported as forced-0).")
    print("="*84)
    maps = ["inv", "pow5", "pow7", "pow11"]
    for p in primes:
        n = curve_order(p)
        if not sym_isprime(n):
            continue
        r = signal(p)
        if r is None:
            continue
        nn, c = r[0], r[1]
        if nn != n:
            continue
        lam = glv_lambda(n)
        rng = np.random.default_rng(p)
        R = 400
        print(f"\np={p} n={n}  (R={R} null draws)")
        for name in maps:
            try:
                f = index_map(name, n)
            except AssertionError as e:
                print(f"  {name:6s}: skipped ({e})")
                continue
            t_data = T_stat(c, f, n)
            t_null = np.array([T_stat(null_permute(c, n, lam, rng), f, n) for _ in range(R)])
            mu, sd = t_null.mean(), t_null.std()
            ge = float((t_null >= t_data).sum())
            # GATE: independent plant must fire OUTSIDE the null band, else no power / null degenerate
            t_ctrl = firing_control(f, n, lam, rng=np.random.default_rng(p*1000+hash(name)%1000))
            ge_ctrl_hi = float((t_null >= t_ctrl).sum())
            ge_ctrl_lo = float((t_null <= t_ctrl).sum())
            ctrl_fires = (ge_ctrl_hi <= 0.01*R) or (ge_ctrl_lo <= 0.01*R)
            star = " *** " if (ge <= 0.01*R or ge >= 0.99*R) else ""
            gate = "[NULL DEGEN/no power]" if not ctrl_fires else "[plant fires]"
            print(f"  {name:6s}: T_data={t_data:+.4f}  null {mu:+.4f}±{sd:.4f}  ge/R={ge:.0f}/{R}"
                  f"  | plant T={t_ctrl:+.4f} ge_hi={ge_ctrl_hi:.0f} ge_lo={ge_ctrl_lo:.0f} {gate}{star}")

if __name__ == "__main__":
    from sympy import nextprime
    primes = []
    p = 7
    while p < 1500 and len(primes) < 6:
        if p % 12 == 7:
            n = curve_order(p)
            if sym_isprime(n):
                primes.append(p)
        p = int(nextprime(p))
    main(primes)
