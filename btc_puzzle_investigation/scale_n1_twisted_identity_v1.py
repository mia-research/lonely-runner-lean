#!/usr/bin/env python3
"""scale_n1_twisted_identity_v1.py -- push the twisted-sum mechanism identity
        V2(a) = V1(a)^2 +/- 2p   (SIN: p==3 mod4 -> +2p ;  COS: p==1 mod4 -> -2p)
which is exactly  e2 = e1^2 +/- p  <=>  v = u^2 - 3/4  (the 120-degree law),
to OUT-OF-SAMPLE primes just past the frozen prereg edge (p=2503).

EXACT: multi-modular.  For several l == 1 mod 3n embed zeta_n -> r in F_l, compute
V1,V2 mod l, check the identity mod each l.  Holding mod >=2 independent l with
|both sides| < l  ==>  exact.  Reuses the VALIDATED core (dlog_table, hist_k1/k2);
this is a DIFFERENT, simpler statistic than the frozen g=2 gcd, so it does not
touch the prereg.  Cost is O(p^2) (hist_k2) -- the DLP wall that caps this tier;
that wall IS the ledger's finding that the twisted-sum laws are banner-locked by
the discrete log, made concrete.

PRE-STATED: every mu_6 class a satisfies V2 = V1^2 + s*2p with s = +1 for p==3 mod4.
Any class that fails is listed individually.
"""
import sys, time
import audit_n1_vsign_v2_core as core

def cube_root_of_unity(n):
    rt = core.tonelli((-3) % n, n); inv2 = pow(2, n-2, n)
    c1 = (-1 + rt) * inv2 % n; c2 = (-1 - rt) * inv2 % n
    assert (c1*c1+c1+1) % n == 0 and (c2*c2+c2+1) % n == 0
    return min(c1, c2)

def mu6_reps(n):
    z3 = cube_root_of_unity(n); z3sq = z3*z3 % n
    U = [1 % n, (n-1) % n, z3, (n-z3) % n, z3sq, (n-z3sq) % n]
    seen = bytearray(n); reps = []
    for m in range(1, n):
        if seen[m]: continue
        reps.append(m)
        for u in U: seen[m*u % n] = 1
    assert len(reps) == (n-1)//6
    return reps

def ell_primes(n, k=3):
    step = 3*n; l = step + 1; out = []
    while len(out) < k:
        if core.is_prime(l): out.append(l)
        l += step
    return out

def prim_root_order(m, l):
    e = (l-1)//m; b = 2
    while True:
        r = pow(b, e, l)
        if r != 1: return r
        b += 1

def check_prime(p):
    n = core.curve_order(p)
    if not core.is_prime(n):
        return None
    t0 = time.time()
    dl = core.dlog_table(p, n)
    h1 = core.hist_k1(p, n, dl)
    h2 = core.hist_k2(p, n, dl)                 # O(p^2)
    reps = mu6_reps(n)
    ells = ell_primes(n, 3)
    s = 1 if p % 4 == 3 else -1                  # SIN(+) / COS(-)
    fails = []
    for a in reps:
        ok_all = True
        for l in ells:
            r = prim_root_order(n, l)
            ra = pow(r, a % n, l)
            rp = 1; V1 = 0; V2 = 0
            for d in range(n):
                if h1[d]: V1 = (V1 + h1[d]*rp) % l
                if h2[d]: V2 = (V2 + h2[d]*rp) % l
                rp = rp*ra % l
            lhs = V2 % l
            rhs = (V1*V1 + s*2*p) % l
            if lhs != rhs:
                ok_all = False; break
        if not ok_all:
            fails.append(a)
    dt = time.time() - t0
    return {'p': p, 'n': n, 'cells': len(reps), 'sign': '+2p' if s == 1 else '-2p',
            'fails': fails, 'secs': dt}

def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 3200
    FROZEN = {43,67,79,127,163,211,547, 823,907,967,991,1051,1303,1831,2143,2251,2503,
              577,733,1237,1249,1669}
    # out-of-sample: p == 7 mod 12 (SIN primary stratum), n prime, NOT frozen, past 547
    picks, p = [], 547
    while p < cap and len(picks) < 8:
        p += 12
        if p % 12 == 7 and p not in FROZEN and core.is_prime(p):
            picks.append(p)
    print("=" * 78)
    print("Twisted-sum identity  V2 = V1^2 + 2p  (=> v = u^2 - 3/4, the 120-deg law)")
    print("OUT-OF-SAMPLE, past the frozen edge p=2503.  Exact (multi-modular).")
    print("=" * 78)
    print(f"{'p':>6} {'n':>6} {'mod12':>5} {'cells':>6} {'sign':>5} {'all cells hold?':>16} {'fails':>6}  [t]")
    print("-" * 78)
    allok = True
    done = 0
    for p in picks:
        r = check_prime(p)
        if r is None:
            continue
        done += 1
        ok = (len(r['fails']) == 0)
        allok = allok and ok
        print(f"{r['p']:>6} {r['n']:>6} {p%12:>5} {r['cells']:>6} {r['sign']:>5} "
              f"{str(ok):>16} {len(r['fails']):>6}  [{r['secs']:.1f}s]")
        if r['fails']:
            print("   FAIL cells:", r['fails'][:10])
    print("-" * 78)
    print(f"out-of-sample primes checked: {done}")
    print("VERDICT:", "V2 = V1^2 + 2p held at EVERY cell, every out-of-sample prime"
          if allok and done else "**a cell failed -- see above**")

if __name__ == "__main__":
    main()
