#!/usr/bin/env python3
"""Forced-triviality of the UNIT/supplement data at ell>=5 (decidable predictions, derived first).

The ell=3 bridge's correction c_3 = s*(e(pibar)-e(nu)) is built from PRIMARIZING UNITS of Z[omega]
(the unit group is mu_6 = {+-1, +-omega, +-omega^2}) plus the omega-SUPPLEMENT chi_lambda(omega),
a separate classical input.

DERIVED PREDICTION (before running): any u in mu_6 satisfies u^6 = 1, so chi_ell(u)^6 = 1; chi_ell(u)
lies in mu_ell which has PRIME order ell.  gcd(6, ell) = 1 for every ell >= 5  =>  chi_ell(u) = 1
FORCED.  So at ell >= 5 the entire unit/primarization layer -- the layer that carries the whole ell=3
correction -- is INVISIBLE to the ell-th power symbol.
Also checks: chi_ell(omega mod nu) == 1, chi_ell(-1 mod nu) == 1.
Exact integers; these are FORCED checks (instrument validity), not evidence."""
import random
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])
from ideal_symbol_build_v1 import omega_mod, elt_mod, sym_exp, build

print("=== FORCED: the mu_6 unit layer is invisible to chi_ell for ell >= 5 ===")
print("    (derived BEFORE running; a pass is an instrument check, not a discovery)\n")
for ell in (3, 5, 7, 11, 13):
    rnd = random.Random(31337)
    rows = build(ell, 200, 26, rnd) if ell != 3 else build(3, 200, 26, rnd)
    if not rows: print(f"  ell={ell}: none"); continue
    N = len(rows); tw = tm1 = tall = 0; d = 0
    for r in rows:
        n, om = r['n'], r['om']
        zn = pow(lpr(n), (n - 1) // ell, n)
        m_om = sym_exp(om, n, ell, zn)              # chi_ell(omega mod nu)
        m_m1 = sym_exp(n - 1, n, ell, zn)           # chi_ell(-1 mod nu)
        if None in (m_om, m_m1): continue
        d += 1
        tw += (m_om == 0); tm1 += (m_m1 == 0)
        # every unit +-omega^k
        ok = True
        for k in range(3):
            for sgn in (1, -1):
                u = (sgn * pow(om, k, n)) % n
                if sym_exp(u, n, ell, zn) != 0: ok = False
        tall += ok
    note = "  <-- ell=3: NOT forced (gcd(6,3)=3), the supplement is live here" if ell == 3 else ""
    print(f"  ell={ell:>2}  chi(omega)=1: {tw}/{d}   chi(-1)=1: {tm1}/{d}   ALL six units trivial: {tall}/{d}{note}")
