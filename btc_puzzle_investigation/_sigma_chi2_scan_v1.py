#!/usr/bin/env python3
"""
_sigma_chi2_scan_v1.py -- follow the two conservations surfaced by isotypic_selection_rule_v1.

Both are exact integer questions, O(p) per prime, no Gram needed. Exact ints only.

(1) B1 = sum_{x in F_p^*} sigma(x)                       [field flap sum]
    B2 = sum_{P != O}     sigma(x_P)                     [curve flap sum]
    C  = sum_{x in F_p}   sigma(x) chi2(x^3+7)           [the character sum]
    identity to verify exactly:  B2 = B1 + C.
    Pre-registered next probe (spec B-iv): is C/sqrt(p) stable across p mod 36?

(2) The <sigma, chi2> pairing, split:
    FLD = sum_x sigma(x) chi2(x)
    CRV = sum_x sigma(x) chi2(x) chi2(x^3+7)
    PREDICTION (derived, falsifiable): under x -> -x,  sigma(-x) = -sigma(x)  and
    chi2(-x) = chi2(-1) chi2(x), so summand(-x) = -chi2(-1)*summand(x). Hence
        p = 1 mod 4  =>  chi2(-1) = +1  =>  FLD = 0 EXACTLY (field negation, NOT in mu6)
        p = 3 mod 4  =>  chi2(-1) = -1  =>  no forced zero
    ANOMALY under test: at p=547 we measured FLD == CRV == -18. Is FLD == CRV general?

Reported per p with (p mod 36, p mod 4, p mod 9, orientation, m mod 2). No pooling.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime, primitive_root
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm

def chi2_table(p):
    qr = bytearray(p)
    for i in range(1, (p - 1) // 2 + 1):
        qr[i * i % p] = 1
    def chi2(v):
        v %= p
        if v == 0: return 0
        return 1 if qr[v] else -1
    return chi2

def build(p):
    R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    def eis(X):
        X %= p
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    def om2(w): u, v = w; return (v - u, -u)
    def reduce_P(a, b):
        c1 = rdiv(a * R2[1] - b * R2[0], DET); c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))
    g = primitive_root(p)
    b1 = pow(g, (p - 1) // 3, p); b2 = pow(b1, 2, p)
    # BETA CALIBRATION -- fixed here; do NOT copy int1_frame_operator_v1.py:41.
    # That line reads:  beta = b1 if eis((b1*12345)%p) == reduce_P(*om2(eis(12345))) else b2
    # i.e. it calibrates on the SINGLE hardcoded probe x=12345. Since 12345 = 3*5*823, at
    # p=823 the probe is x=0, the test degenerates to (0,0)==(0,0), and b1 is returned with
    # NOTHING tested. At p=823 that picks the wrong root: the exact omega^2 relation then
    # holds for 0/822 x and eps==2 for 822/823 (vs the correct root: 822/822, eps in {0,1},
    # flap 204/822 = 0.248 ~ the Cap Law 1/4). Verified 2026-07-17.
    # Fix: require the relation on MANY nonzero x and assert exactly one root qualifies.
    probes = [x for x in range(1, min(p, 40))]
    ok1 = all(eis(b1 * x % p) == reduce_P(*om2(eis(x))) for x in probes)
    ok2 = all(eis(b2 * x % p) == reduce_P(*om2(eis(x))) for x in probes)
    assert ok1 != ok2, f"beta calibration ambiguous at p={p}: ok1={ok1} ok2={ok2}"
    beta = b1 if ok1 else b2
    def eps(X):
        U0 = eis(X); U1 = eis((beta * X) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 0
        if c in (tuple(R1), tuple(R2), (-R1[0], -R1[1]), (-R2[0], -R2[1])): return 1
        return 2
    return eis, eps, beta, R1, R2, DET

def sigma_fn(p, eis, eps, R1, R2, DET):
    """sigma with the orientation fixed by a 100%-agreement PRE-FLIGHT (not a majority vote).
    Returns (sigma, orient) or (None, None) if neither orientation agrees on every x."""
    def co(w):
        a, b = w
        return Fr(a * R2[1] - b * R2[0], DET), Fr(b * R1[0] - a * R1[1], DET)
    for cand in ('-', '+'):
        ok = True
        for x in range(p):
            u, v = co(eis(x))
            s = (u - v) if cand == '-' else (u + v)
            if (abs(s) > Fr(1, 2)) != (eps(x) != 0):
                ok = False; break
        if not ok: continue
        def sig(x, cand=cand):
            u, v = co(eis(x))
            s = (u - v) if cand == '-' else (u + v)
            if abs(s) <= Fr(1, 2): return 0
            return 1 if s > 0 else -1
        return sig, cand
    return None, None

def scan_prime(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return {'p': p, 'FAIL': 'no orientation agrees with eps on all x'}
    w = [chi2(((x * x % p) * x + 7) % p) for x in range(p)]
    sg = [sig(x) for x in range(p)]
    c2 = [chi2(x) for x in range(p)]
    B1 = sum(sg[1:])
    C = sum(sg[x] * w[x] for x in range(p))
    B2 = B1 + C
    FLD = sum(sg[x] * c2[x] for x in range(p))
    CRV = sum(sg[x] * c2[x] * w[x] for x in range(p))
    flap = sum(1 for x in range(p) if eps(x) != 0)
    # independent recompute of B2 directly over the curve, to verify the identity honestly
    B2_direct = 0
    for x in range(p):
        B2_direct += sg[x] * (1 + w[x])
    return {'p': p, 'n': n, 'm': (n - 1) // 6, 'pmod36': p % 36, 'pmod4': p % 4,
            'pmod9': p % 9, 'orient': orient, 'B1': B1, 'B2': B2, 'C': C,
            'B2_direct': B2_direct, 'FLD': FLD, 'CRV': CRV, 'flap': flap,
            'eps2': sum(1 for x in range(p) if eps(x) == 2)}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    rows = []
    skipped = 0
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = scan_prime(p)
        if r is None:
            skipped += 1; continue
        rows.append(r)
    print(f"# primes p in [{lo},{hi}), p=1 mod 6, n prime. kept={len(rows)} skipped(n composite)={skipped}")
    print(f"# {'p':>6} {'m36':>4} {'m4':>3} {'m9':>3} {'or':>3} {'flap':>6} {'B1':>4} {'C':>6} {'B2':>6} "
          f"{'FLD':>6} {'CRV':>6} {'FLD==CRV':>9} {'C^2/p':>9}")
    for r in rows:
        if 'FAIL' in r:
            print(f"  {r['p']:>6}  FAIL: {r['FAIL']}"); continue
        assert r['B2'] == r['B2_direct'], f"identity B2=B1+C FAILED at p={r['p']}"
        # Weil reference reported EXACTLY: C^2/p as a rational (no float, no carve-out needed).
        # |C| <= ||sigma||_W * 2 sqrt(p)  <=>  C^2/p <= (2 ||sigma||_W)^2.
        c2p = Fr(r['C'] * r['C'], r['p'])
        print(f"  {r['p']:>6} {r['pmod36']:>4} {r['pmod4']:>3} {r['pmod9']:>3} {r['orient']:>3} "
              f"{r['flap']:>6} {r['B1']:>4} {r['C']:>6} {r['B2']:>6} {r['FLD']:>6} {r['CRV']:>6} "
              f"{str(r['FLD']==r['CRV']):>9} {str(c2p.limit_denominator(100)):>9}")
    # the two pre-registered questions
    print()
    ok1 = all(r['B1'] == 0 for r in rows if 'FAIL' not in r)
    print(f"B1 == 0 at every prime (PROVED: sigma odd + F_p^* negation-closed): {ok1}")
    p1 = [r for r in rows if 'FAIL' not in r and r['pmod4'] == 1]
    p3 = [r for r in rows if 'FAIL' not in r and r['pmod4'] == 3]
    print(f"PREDICTION  p=1 mod 4 => FLD==0 : {all(r['FLD']==0 for r in p1)}  (n={len(p1)})")
    print(f"            p=3 mod 4 => FLD!=0 : {sum(1 for r in p3 if r['FLD']!=0)}/{len(p3)} nonzero")
    eq = [r for r in rows if 'FAIL' not in r and r['FLD'] == r['CRV']]
    print(f"ANOMALY     FLD == CRV          : {len(eq)}/{len([r for r in rows if 'FAIL' not in r])} primes")
    eq3 = [r for r in p3 if r['FLD'] == r['CRV']]
    print(f"            FLD == CRV | p=3(4) : {len(eq3)}/{len(p3)}")
    eq1 = [r for r in p1 if r['FLD'] == r['CRV']]
    print(f"            FLD == CRV | p=1(4) : {len(eq1)}/{len(p1)}")
    z = [r for r in rows if 'FAIL' not in r and r['C'] == 0]
    print(f"C == 0 (would be the strongest outcome, B-v): {len(z)}/{len(rows)}")

if __name__ == '__main__':
    main()
