#!/usr/bin/env sage
# d2_nonabelian_sweep_v2.sage — widen RESULT_anew_twisted_eigenvalues_nonabelian_v1.md
# (was: p=43, 67 generic FAIL + p=13 small-case pass) to new primes, BOTH mod-12 arms,
# at a=1 (and a=2 spot checks). Same machinery as anew_eigenvalue_verify_v4.sage:
# factor L* over Q(zeta_{12n}); [2,2] -> discriminant Galois-test sigma(D)/D in K^2.
# Plants validated in each field (D=5 abelian / D=zeta+2 non-abelian).
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core
try:
    pari.allocatemem(1 << 33)   # 8GB: p=211 (phi=792) overflowed the 1GB default
except Exception as e:
    print(f"[pari.allocatemem failed: {e}]", flush=True)

def unit_gens_fallback(m):
    try:
        return [Integer(g) for g in Zmod(m).unit_gens()]
    except Exception:
        from math import gcd
        units = [g for g in range(2, m) if gcd(g, m) == 1]
        # greedy generating subset
        gens = []
        cur = {1}
        target = len(units) + 1
        for g in units:
            if len(cur) >= target:
                break
            nxt = set(x * g % m for x in cur) | cur
            if len(nxt) > len(cur):
                gens.append(Integer(g))
                cur = nxt
        return gens

def galois_test(D, K, z, m, verbose=False):
    for t in unit_gens_fallback(m):
        r = (K.hom([z**t])(D) / D)
        if not r.is_square():
            return False, t
    return True, None

def build_L(p, a, K, z, n):
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    V1 = sum(h1[d]*z**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*z**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = K(p**2)
    R = PolynomialRing(K, 'T'); T = R.gen()
    return T**4 - e1*T**3 + e2*T**2 - e3*T + e4

def run(p, a=1):
    t0 = time.time()
    n = core.curve_order(p); m = 12*n
    K = CyclotomicField(m); z = K.gen()
    Kn = CyclotomicField(n); zn = Kn.gen()
    L = build_L(p, a, Kn, zn, n)
    phi = Kn.hom([z**12], K)
    R = PolynomialRing(K, 'T'); T = R.gen()
    Lb = sum(phi(c)*T**i for i, c in enumerate(L.list()))
    facs = [f for f, e in Lb.factor()]
    degs = sorted(f.degree() for f in facs)
    print(f"p={p} n={n} a={a} [phi(12n)={K.degree()}] factor degs = {degs}", flush=True)
    if degs != [2, 2]:
        print(f"    (non-[2,2] factorization -- report only)", flush=True)
        return
    okabel, _ = galois_test(K(5), K, z, m)
    oknon, _ = galois_test(z + 2, K, z, m)
    print(f"    [plants: D=5 galois={okabel} (want True) | D=zeta+2 galois={oknon} (want False)]", flush=True)
    for i, q in enumerate(facs):
        D = q[1]**2 - 4*q[0]
        if D.is_square():
            print(f"    quad {i}: D square -> eigenvalues in Q(zeta_{m}) (ABELIAN/cyclotomic!)", flush=True)
            continue
        gal, t = galois_test(D, K, z, m)
        print(f"    quad {i}: Galois(sigma(D)/D in K^2) = {gal}" +
              (f" (FAILS at sigma_{t}) -> NON-ABELIAN" if not gal else " -> could be abelian"), flush=True)
    print(f"    [{time.time()-t0:.1f}s]", flush=True)

for p in (211, 349):
    try:
        run(p, 1)
    except Exception as e:
        print(f"p={p}: FAILED ({type(e).__name__}: {e})", flush=True)
try:
    run(61, 2)   # a-spread spot check (61 is cheap: 62s)
except Exception as e:
    print(f"p=61 a=2: FAILED ({e})", flush=True)
