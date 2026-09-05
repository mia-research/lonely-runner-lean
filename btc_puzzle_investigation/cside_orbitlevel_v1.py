#!/usr/bin/env python3
# cside_orbitlevel_v1.py -- the c-side non-algebraic correlation, at ORBIT LEVEL, scalable to large p.
#
# KEY REDUCTION (verified): c is constant on each mu_3 orbit (GLV invariance c(lam*d)=c(d), forced).
# inv and pow-k maps each map orbits to orbits. So c(d)c(f(d)) depends only on (orbit(d), orbit(f(d))).
# Effective sample size = number of orbits = (n-1)/6 (with oddness) -- THIS is what determines power,
# not n. Small p has ~5-33 orbits => no power (confirmed). Large p (orbits ~1e4-1e5) => real power.
#
# OBJECT. T_f = mean over orbit-reps r of  c(r) * c(f-orbit(r)),  where c(r) in {-1,+1} is the
# constant value on orbit r. f-orbit = the orbit that f maps r to. Equivalent to the full sum.
#
# NULL. Permute the orbit-rep VALUE labels (which +/-1 sits on which orbit), preserving oddness sign.
# R draws. Plant: a fresh random orbit-value assignment with a known f-orbit correlation.
#
# GATE (must fire before any data is trusted): the plant must land outside the null band.
import sys, numpy as np
from sympy import primitive_root, nextprime, isprime as sym_isprime

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from twist_orbit_spectrum_run_v1 import signal

def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1

def curve_order(p, B=7):
    n = p + 1
    for x in range(p): n += legendre((x*x % p * x + B) % p, p)
    return n

def build_orbits(n, lam):
    """Return (rep_of, orbit_list, norbits). rep_of[d] = index of orbit containing d (d in 1..n-1).
    Each orbit = {d, lam d, lam^2 d} (size 3); oddness pairs orbit r with a 'negated' partner but
    values are +/-1 so we treat the (n-1)/3 mu_3 orbits as the free units, oddness fixing the sign
    of the -d copy. We index orbits 0..(n-1)/3-1."""
    seen = set(); rep_of = {}; orbits = []
    for d in range(1, n):
        if d in seen: continue
        orb = sorted([d, (d*lam) % n, (d*lam*lam) % n])
        for x in orb:
            seen.add(x); rep_of[x] = len(orbits)
        orbits.append(orb)
    return rep_of, orbits, len(orbits)

def orbit_map_f(n, lam, rep_of, fname):
    """For each orbit index r, return the orbit index that f maps the orbit's rep to."""
    from math import gcd
    def fval(d):
        if fname == 'inv': return pow(d, n-2, n)
        k = int(fname[3:]); assert gcd(k, n-1) == 1; return pow(d, k, n)
    fmap = []
    for orb in [None]:  # placeholder
        pass
    out = {}
    for d, r in rep_of.items():
        out[r] = rep_of[fval(d)]
    return out  # orbit-index -> orbit-index

def run_prime(p, maps, R=600):
    n = curve_order(p)
    if not sym_isprime(n): return None
    r = signal(p)
    if r is None: return None
    nn, c = r[0], r[1]
    if nn != n: return None
    g = int(primitive_root(n)); lam = pow(g, (n-1)//3, n)
    rep_of, orbits, norb = build_orbits(n, lam)
    # orbit values: c is constant on orbit; take c[orb[0]]
    val = np.array([c[orb[0]] for orb in orbits], dtype=np.int64)   # +/-1 per orbit
    # oddness check: c[-d] should equal -c[d]; the negated orbit has opposite sign. We work with
    # the mu_3 orbits directly; the statistic over orbits is well-defined.
    print(f"\np={p} n={n} orbits={norb} (free units)")
    rng = np.random.default_rng(p)
    out = {}
    for fname in maps:
        try:
            fmap = orbit_map_f(n, lam, rep_of, fname)
        except (AssertionError, KeyError) as e:
            print(f"  {fname:6s}: skipped ({e})"); continue
        fidx = np.array([fmap[r] for r in range(norb)], dtype=np.int64)
        # statistic: mean over orbits of val[r]*val[fidx[r]]
        def Tstat(v):
            return float((v * v[fidx]).mean())      # noqa: float (ranked vs null)
        t_data = Tstat(val)
        # null: permute orbit value labels
        t_null = np.empty(R)
        for i in range(R):
            vp = val.copy(); rng.shuffle(vp)
            t_null[i] = Tstat(vp)
        mu, sd = t_null.mean(), t_null.std()
        ge = float((t_null >= t_data).sum())
        # GATE: independent plant -- DECISIVE known f-correlation. Force a fraction 'agree' of
        # orbits to have val == val[fidx]; the rest random. agree=0.8 => strong, detectable signal.
        rp = np.random.default_rng(p*1000+sum(ord(ch) for ch in fname))
        agree = 0.8
        vplant = rp.choice([-1,1], size=norb)
        # pick 'agree' fraction of orbits and set their f-image equal
        nagree = int(agree*norb)
        idx = rp.choice(norb, size=nagree, replace=False)
        for ii in idx:
            vplant[fidx[ii]] = vplant[ii]
        t_plant = Tstat(vplant)
        ge_p_hi = float((t_null >= t_plant).sum()); ge_p_lo = float((t_null <= t_plant).sum())
        fires = (ge_p_hi <= 0.01*R) or (ge_p_lo <= 0.01*R)
        star = " *** " if (ge <= 0.01*R or ge >= 0.99*R) else ""
        gate = "[plant fires]" if fires else "[NO POWER]"
        print(f"  {fname:6s}: T_data={t_data:+.4f}  null {mu:+.4f}±{sd:.4f}  ge={ge:.0f}/{R}  "
              f"| plant T={t_plant:+.4f} ge_hi={ge_p_hi:.0f} ge_lo={ge_p_lo:.0f} {gate}{star}")
        out[fname] = dict(t_data=t_data, ge=ge, fires=fires)
    return out

if __name__ == "__main__":
    maps = ["inv", "pow5", "pow7", "pow11", "pow13"]
    # small primes first to confirm orbit-count scaling, then a large one for power
    from sympy import nextprime
    test_p = []
    p = 7
    while p < 600 and len(test_p) < 3:
        if p % 12 == 7:
            n = curve_order(p)
            if sym_isprime(n): test_p.append(p)
        p = int(nextprime(p))
    # add a large prime (orbits ~ 1600)
    p = 10000
    import time; t0=time.time()
    while p < 30000 and time.time()-t0 < 120:
        if p % 12 == 7:
            n = curve_order(p)
            if sym_isprime(n):
                test_p.append(p); break
        p = int(nextprime(p))
    for p in test_p:
        run_prime(p, maps)
