#!/usr/bin/env python3
"""AUDIT of RESULT_jacobi_sign_law_semiprimitive_v1. Checks that can FALSIFY it.
A: validate the Gauss-sum code INDEPENDENTLY of (S), via g(chi)*g(chi_bar) = chi(-1)*q.
   (I edited the reduction AFTER seeing a wrong answer -> must not validate it against (S) itself.)
B: is J = g(chi3)g(chi4)/g(chi3*chi4) actually true numerically, with the CORRECT product character?
D: does g depend ONLY on the order d?  (S) assumes it; chi3*chi4 = chi12^7 in my indexing, NOT chi12.
"""
exec(open('jacobi_semiprimitive_v1.py').read().split('print("=== (S)')[0])

def gauss_e(p, e12, els, dlog):
    """Gauss sum of the character g^k -> zeta_12^(k*e12). Returns int, or the raw vector if not rational."""
    coeff = [ZERO[:] for _ in range(p)]
    for x in els:
        coeff[(2*x[0]) % p] = zadd(coeff[(2*x[0]) % p], zpow_zeta12((dlog[x]*e12) % 12))
    diffs = [zsub(coeff[t], coeff[0]) for t in range(1, p)]
    v = diffs[0]
    if any(d != v for d in diffs): return None
    m = [-c for c in v]
    return m[0] if is_rat_int(m) else m

def zconj(a):
    """complex conjugation on Z[zeta_12]: zeta_12 -> zeta_12^11."""
    r = ZERO[:]
    for i, c in enumerate(a):
        if c: r = zadd(r, [c*t for t in zpow_zeta12((11*i) % 12)])
    return r

PRIMES = [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83]
print("=== A: INDEPENDENT validation  g(chi)*conj(g(chi)) == chi(-1)*q,  q=p^2  (no reference to (S)) ===")
print(f"  {'p':>4} {'d':>3} {'chi(-1)':>8} {'g*conj(g)':>10} {'chi(-1)*q':>10}  ok")
okA = True
for p in PRIMES:
    els, dlog, order = build_field(p)
    for d in (2, 3, 4, 6, 12):
        if (p+1) % d: continue
        e12 = 12 // d
        g = gauss_e(p, e12, els, dlog)
        gv = g if isinstance(g, list) else [g, 0, 0, 0]
        prod = zmul(gv, zconj(gv))
        km1 = dlog[((-1) % p, 0)]
        chim1 = zpow_zeta12((km1*e12) % 12)
        want = [c*p*p for c in chim1]
        ok = (prod == want); okA &= ok
        cm = chim1[0] if is_rat_int(chim1) else chim1
        pv = prod[0] if is_rat_int(prod) else prod
        wv = want[0] if is_rat_int(want) else want
        print(f"  {p:>4} {d:>3} {str(cm):>8} {str(pv):>10} {str(wv):>10}  {'OK' if ok else 'FAIL'}")
print(f"  --> Gauss-sum code validated independently of (S): {okA}")

print("\n=== D: does g depend ONLY on the order d?  (compare all primitive chars of order d) ===")
print(f"  {'p':>4} {'d':>3} {'g over all primitive chars of order d':>44}  all equal?")
okD = True
for p in PRIMES:
    els, dlog, order = build_field(p)
    for d in (3, 4, 12):
        if (p+1) % d: continue
        vals = []
        for a in range(1, d):
            if __import__('math').gcd(a, d) != 1: continue
            vals.append(gauss_e(p, (12//d)*a % 12, els, dlog))
        eq = all(v == vals[0] for v in vals); okD &= eq
        print(f"  {p:>4} {d:>3} {str(vals):>44}  {'YES' if eq else 'NO'}")
print(f"  --> g is order-only in every tested cell: {okD}")

print("\n=== B: is  J(chi3,chi4) == g(chi3)*g(chi4)/g(chi3*chi4)  with the CORRECT product char? ===")
print("    NOTE chi3*chi4 = zeta_12^(4k+3k) = zeta_12^(7k)  => e12 = 7, NOT the e12=1 'chi12' I used.")
print(f"  {'p':>4} {'p%12':>5} {'g3':>6} {'g4':>6} {'g(3*4)':>16} {'g3*g4/g(3*4)':>14} {'J direct':>10}  ok")
okB = True
for p in PRIMES:
    els, dlog, order = build_field(p)
    g3 = gauss_e(p, 4, els, dlog); g4 = gauss_e(p, 3, els, dlog)
    g34 = gauss_e(p, 7, els, dlog)                      # chi3*chi4
    J = jacobi(p, 3, 4, els, dlog, order)
    Jv = J[0] if is_rat_int(J) else J
    if isinstance(g3, int) and isinstance(g4, int) and isinstance(g34, int) and g34 != 0:
        ratio = (g3*g4)//g34 if (g3*g4) % g34 == 0 else (g3*g4)/g34
        ok = (ratio == Jv); okB &= ok
        print(f"  {p:>4} {p%12:>5} {str(g3):>6} {str(g4):>6} {str(g34):>16} {str(ratio):>14} {str(Jv):>10}  {'OK' if ok else 'FAIL'}")
    else:
        print(f"  {p:>4} {p%12:>5} {str(g3):>6} {str(g4):>6} {'NOT RATIONAL':>16} {'n/a':>14} {str(Jv):>10}  (skip)")
print(f"  --> decomposition verified wherever all three are rational: {okB}")
