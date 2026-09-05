#!/usr/bin/env python3
"""IDEAL-LEVEL STRUCTURE: forced facts only (no inference, no association statistic).

Checks, all decidable:
 F1  pi == 1 (mod nu)  =>  chi_ell(pi mod nu) == 1 identically  [explains m_pi==0, 400/400]
 F2  hence  chi_ell(p mod n) == chi_ell(pibar mod nu)   -- the rational symbol IS a single CM-factor
     symbol; the CM factorization does NOT refine it.
 F3  the mirror side: nu == 1 (mod pi)  =>  chi_ell(n mod p) == chi_ell(nubar mod pi).
 F4  CONJUGATE PRIMES.  The ell-1 primes of O_L (L = Q(zeta_3ell)) above nu correspond to the ell-1
     primitive ell-th roots of unity mod n.  If the symbol exponent w.r.t. root z is m, then w.r.t.
     z^c it is m*c^{-1}.  => product over all conjugate primes = zeta^(m * sum_{c in (Z/ell)*} c^{-1})
     = 1 FORCED (sum of all units mod ell is 0 for ell>2).  So the symbol of the IDEAL (nu) in O_L is
     trivially 1, carrying no information; all content sits in the INDIVIDUAL conjugate exponent m.
Exact integers throughout."""
import random
from collections import Counter
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])
from ideal_symbol_build_v1 import omega_mod, elt_mod, sym_exp, build

def prim_ell_roots(n, ell):
    """all ell-1 primitive ell-th roots of unity in F_n (n == 1 mod ell)."""
    z = pow(lpr(n), (n - 1) // ell, n)
    return [pow(z, c, n) for c in range(1, ell)]

print("=== FORCED STRUCTURE of the ideal-level CM-factor symbol ===\n")
for ell in (5, 7, 11, 13):
    rnd = random.Random(31337)
    rows = build(ell, 250, 26, rnd)
    if not rows: print(f"  ell={ell}: none"); continue
    N = len(rows)
    # F1: pi mod nu == 1
    f1 = sum(1 for r in rows if r['xpi'] % r['n'] == 1)
    # F2: chi(p mod n) == chi(pibar mod nu)
    f2 = sum(1 for r in rows if r['m_p'] == r['m_pb'])
    # F3 mirror: nu mod pi == 1 in Z[omega]/(pi) = F_p, and chi(n mod p) == chi(nubar mod pi)
    f3 = f3d = 0
    for r in rows:
        p, n, t, vs = r['p'], r['n'], r['t'], r['v']
        pa, pb = (t + vs) // 2, vs                 # pi
        na, nb = 1 - pa, -pb                       # nu = 1-pi
        ca, cb = na - nb, -nb                      # nubar
        omp = omega_mod(pa, pb, p)                 # image of omega in Z[omega]/(pi) = F_p
        if omp is None or (omp*omp + omp + 1) % p != 0: continue
        xnu = elt_mod(na, nb, omp, p); xnb = elt_mod(ca, cb, omp, p)
        if xnu % p == 0 or xnb % p == 0: continue
        zp = pow(lpr(p), (p - 1) // ell, p)
        m_n  = sym_exp(n % p, p, ell, zp)
        m_nb = sym_exp(xnb, p, ell, zp)
        if None in (m_n, m_nb): continue
        f3d += 1
        f3 += (xnu % p == 1) and (m_n == m_nb)
    # F4: conjugate-prime exponents m*c^{-1}, and forced product == 1
    f4t = f4p = 0
    for r in rows[:60]:
        n, ell_ = r['n'], ell
        roots = prim_ell_roots(n, ell_)
        z0 = roots[0]
        m0 = sym_exp(r['xpb'], n, ell_, z0)
        exps = [sym_exp(r['xpb'], n, ell_, zc) for zc in roots]
        if None in exps or m0 is None: continue
        # transformation: w.r.t. z0^c the exponent must be m0 * c^{-1} mod ell
        ok = all(exps[c-1] == (m0 * pow(c, -1, ell_)) % ell_ for c in range(1, ell_))
        f4t += ok
        f4p += (sum(exps) % ell_ == 0)             # product over conjugates == 1
    print(f"  ell={ell:>2} N={N:>4}")
    print(f"     F1  pi == 1 mod nu (=> chi(pi)=1 forced)          : {f1}/{N}")
    print(f"     F2  chi(p mod n) == chi(pibar mod nu)             : {f2}/{N}")
    print(f"     F3  nu == 1 mod pi AND chi(n mod p)==chi(nubar)   : {f3}/{f3d}")
    print(f"     F4a conjugate exponents follow m*c^-1             : {f4t}/60")
    print(f"     F4b product over conjugate primes == 1 (FORCED)   : {f4p}/60")
