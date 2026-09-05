#!/usr/bin/env python3
"""Does the CM generator's residue reduce to a RATIONAL integer?  (decidable, derived first)

From nu = 1 - pi and pi + pibar = t:
    pibar = t - pi = t - (1 - nu) = (t-1) + nu  ==  t-1  (mod nu)
    nubar = 1 - pibar = 1 - (t - pi) = (1-t) + pi ==  1-t (mod pi)
If these hold ELEMENT-WISE in Z[omega], then chi_ell(pibar mod nu) = chi_ell((t-1) mod n) is the symbol
of a RATIONAL integer -- i.e. both sides of the bridge are symbols of the same rational U = |t-1|, in
two different fields, and there is no ideal-level content beyond that.
Also records: how often the two sides' arguments agree up to sign (U vs -U).
Exact integers; FORCED checks (instrument validity), not evidence."""
import random
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])
from ideal_symbol_build_v1 import omega_mod, elt_mod, sym_exp, build

print("=== Does pibar reduce to the RATIONAL integer t-1 mod nu? (and the mirror) ===\n")
for ell in (5, 7, 11, 13):
    rnd = random.Random(31337)
    rows = build(ell, 250, 26, rnd)
    if not rows: print(f"  ell={ell}: none"); continue
    N = len(rows); r1 = r2 = r3 = r4 = 0; d = 0
    for r in rows:
        p, n, t, vs = r['p'], r['n'], r['t'], r['v']
        pa, pb = (t + vs) // 2, vs                  # pi
        qa, qb = pa - pb, -pb                       # pibar
        na, nb = 1 - pa, -pb                        # nu = 1 - pi
        ca, cb = na - nb, -nb                       # nubar
        om_n = omega_mod(na, nb, n)                 # omega in Z[omega]/(nu) = F_n
        om_p = omega_mod(pa, pb, p)                 # omega in Z[omega]/(pi)  = F_p
        if om_n is None or om_p is None: continue
        if (om_n*om_n + om_n + 1) % n != 0: continue
        if (om_p*om_p + om_p + 1) % p != 0: continue
        d += 1
        # R1: pibar == t-1 (mod nu)   [element-wise, in F_n]
        r1 += (elt_mod(qa, qb, om_n, n) - (t - 1)) % n == 0
        # R2: nubar == 1-t (mod pi)   [element-wise, in F_p]
        r2 += (elt_mod(ca, cb, om_p, p) - (1 - t)) % p == 0
        # R3/R4: consequently the two bridge sides are symbols of the SAME rational U, opposite signs
        zn = pow(lpr(n), (n - 1) // ell, n); zp = pow(lpr(p), (p - 1) // ell, p)
        a1 = sym_exp((t - 1) % n, n, ell, zn); b1 = sym_exp(p % n, n, ell, zn)
        a2 = sym_exp((1 - t) % p, p, ell, zp); b2 = sym_exp(n % p, p, ell, zp)
        if None not in (a1, b1): r3 += (a1 == b1)
        if None not in (a2, b2): r4 += (a2 == b2)
    print(f"  ell={ell:>2} N={d}")
    print(f"     R1  pibar == t-1  (mod nu), element-wise in Z[omega] : {r1}/{d}")
    print(f"     R2  nubar == 1-t  (mod pi), element-wise in Z[omega] : {r2}/{d}")
    print(f"     R3  chi_ell(p mod n) == chi_ell((t-1) mod n)         : {r3}/{d}")
    print(f"     R4  chi_ell(n mod p) == chi_ell((1-t) mod p)         : {r4}/{d}")
