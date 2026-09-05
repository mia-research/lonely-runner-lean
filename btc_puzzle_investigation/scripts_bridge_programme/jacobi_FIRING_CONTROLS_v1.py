#!/usr/bin/env python3
"""FIRING CONTROLS for RESULT_jacobi_sign_law_semiprimitive_v1 -- the gap named in its sec 0a.
Checks (A) and (D) showed the code is SELF-CONSISTENT.  They did not show it can REJECT a false input.
An instrument never shown to fire gives weak agreements.  These four controls fire it deliberately."""
exec(open('jacobi_semiprimitive_v1.py').read().split('print("=== (S)')[0])
import math
PRIMES = [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 83]

def gauss_e(p, e12, els, dlog):
    coeff = [ZERO[:] for _ in range(p)]
    for x in els:
        coeff[(2*x[0]) % p] = zadd(coeff[(2*x[0]) % p], zpow_zeta12((dlog[x]*e12) % 12))
    diffs = [zsub(coeff[t], coeff[0]) for t in range(1, p)]
    v = diffs[0]
    if any(d != v for d in diffs): return None
    m = [-c for c in v]
    return m[0] if is_rat_int(m) else m
def zconj(a):
    r = ZERO[:]
    for i, c in enumerate(a):
        if c: r = zadd(r, [c*t for t in zpow_zeta12((11*i) % 12)])
    return r

print("=== FC1: does the code DISCRIMINATE?  non-semiprimitive d (d | p-1, NOT d | p+1) ===")
print("    (S) claims g = +-p only for d | p+1.  If the code returned +-p for d | p-1 too, it would be")
print("    reporting a constant regardless of input -> the 43/43 would be vacuous.")
print(f"  {'p':>4} {'d':>3} {'d|p+1?':>7} {'d|p-1?':>7} {'g rational?':>12} {'value':>10}")
fired = 0; tested = 0
for p in PRIMES:
    els, dlog, order = build_field(p)
    for d in (3, 4, 6, 12):
        if (p+1) % d == 0: continue          # want the NON-semiprimitive case
        if (p-1) % d != 0: continue
        tested += 1
        g = gauss_e(p, 12//d, els, dlog)
        rat = isinstance(g, int)
        if not rat or abs(g) != p: fired += 1
        print(f"  {p:>4} {d:>3} {'no':>7} {'yes':>7} {str(rat):>12} {str(g if rat else 'NOT RATIONAL'):>10}")
print(f"  --> code did NOT return +-p in {fired}/{tested} non-semiprimitive cells: "
      f"{'CONTROL FIRES (it discriminates)' if fired == tested and tested > 0 else 'DID NOT FIRE'}")

print("\n=== FC2: can check (A) g*conj(g) = chi(-1)*q FAIL?  (plant a CORRUPTED character) ===")
print("    (A) was used to validate the code independently of (S). If (A) can never fail it is vacuous.")
okfail = 0; n = 0
for p in PRIMES[:6]:
    els, dlog, order = build_field(p)
    # corrupt: use a NON-character map  x -> zeta_12^(dlog(x)^2 * e12)  (not multiplicative)
    coeff = [ZERO[:] for _ in range(p)]
    for x in els:
        coeff[(2*x[0]) % p] = zadd(coeff[(2*x[0]) % p], zpow_zeta12((dlog[x]*dlog[x]*3) % 12))
    diffs = [zsub(coeff[t], coeff[0]) for t in range(1, p)]
    v = diffs[0]
    g = None if any(d != v for d in diffs) else [-c for c in v]
    n += 1
    if g is None:
        okfail += 1; verdict = "rejected (not rational) -> (A) unreachable, still a rejection"
    else:
        prod = zmul(g, zconj(g)); km1 = dlog[((-1) % p, 0)]
        want = [c*p*p for c in zpow_zeta12((km1*3) % 12)]
        if prod != want: okfail += 1; verdict = "(A) FAILS on the corrupted input"
        else: verdict = "(A) PASSED on corrupted input -- BAD"
    print(f"  p={p:>3}  {verdict}")
print(f"  --> corrupted input rejected in {okfail}/{n} cells: "
      f"{'CONTROL FIRES ((A) is not vacuous)' if okfail == n else 'DID NOT FIRE'}")

print("\n=== FC3: would a WRONG sign rule have been caught?  test (S') = -(S) ===")
agree_S = agree_Sbad = tot = 0
for p in PRIMES:
    els, dlog, order = build_field(p)
    for d in (2, 3, 4, 6, 12):
        if (p+1) % d: continue
        g = gauss_e(p, 12//d, els, dlog); tot += 1
        agree_S    += (g == (-1)**((p+1)//d) * p)
        agree_Sbad += (g == -((-1)**((p+1)//d)) * p)
print(f"  (S)  correct sign rule : {agree_S}/{tot} agree")
print(f"  (S') flipped sign rule : {agree_Sbad}/{tot} agree")
print(f"  --> {'CONTROL FIRES (the check discriminates sign rules)' if agree_Sbad < tot//4 else 'DID NOT FIRE'}")

print("\n=== FC4: would a wrong J sign have been caught? plant J := -J at p = 11 mod 12 ===")
bad = 0; tot4 = 0
for p in PRIMES:
    if p % 12 != 11: continue
    els, dlog, order = build_field(p)
    J = jacobi(p, 3, 4, els, dlog, order); Jv = J[0] if is_rat_int(J) else None
    tot4 += 1
    if Jv is not None and -Jv != p: bad += 1     # the planted wrong value must NOT equal the prediction
print(f"  planted J = -J disagrees with the +p prediction in {bad}/{tot4} cells: "
      f"{'CONTROL FIRES' if bad == tot4 else 'DID NOT FIRE'}")
