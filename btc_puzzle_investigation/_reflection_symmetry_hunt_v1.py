#!/usr/bin/env python3
"""
_reflection_symmetry_hunt_v1.py -- follow the S conservation to its deeper symmetry (mantra).

THE CONSERVATION (v34 s.4, EMPIRICAL 35/35): <sigma,chi2>_FIELD = 0 <=> p != 3 mod 8. The
p=7 mod 8 case (35/35) is NOT forced by the mu6 selection rule. Last session RULED OUT the natural
mechanism: NO multiplicative c in F_p^* with sigma*chi2(cx) = -sigma*chi2(x).

RULE 13 (anomaly-drill memory): name the NEXT candidate mechanism and try to KILL it.

THE CANDIDATE. The hexagonal lattice L=(pi_p) has symmetry group D_6 (order 12):
  * 6 ROTATIONS  z -> zeta6^k z  -- these descend to F_p as multiplication by mu6. Already known.
  * 6 REFLECTIONS z -> zeta6^k zbar -- conjugation composed with rotation.
The reflections do NOT descend to F_p as multiplications, because Lbar = (pi_p bar) != (pi_p)
(conjugation maps E's coordinate ring to the CONJUGATE prime = the amicable partner / twist). This
is exactly why the multiplicative search missed it -- the missing involution is a REFLECTION, and it
points OUTSIDE F_p's rotational symmetry (mantra: "structure happens outside the symmetry").

CONSTRUCTION. eis: F_p -> Z[omega] cap P,  x |-> (u,v) meaning x = u + v*omega_p mod p, where
omega_p in F_p is the image of omega (a primitive cube root of 1). Conjugation omega -> omega^2
sends the field element to  tau(x) := (u + v*omega_p^2) mod p. This is a total, computable map.
Compose with the 6 rotations to get all 6 reflection-type maps  R_k(x) := beta^k * tau(x).

KILL-CONDITION (decidable, exact, over ALL x -- no statistical null needed):
  a reflection R explains S  iff  for all x:  sigma(R x) = -sigma(x)  AND  chi2(R x) = chi2(x)
  (=> sigma*chi2(Rx) = -sigma*chi2(x) => the flap orbits pair up with opposite sign => S=0),
  and R is an involution with the right fixed-point structure (fixed pts <-> ORB parity <-> H1).
If NO reflection does this, the candidate is KILLED and the next probe is named.

Exact ints throughout (eis, omega_p, sigma, chi2 all exact). No float in the signal path.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def omega_p_of(p, eis):
    """omega_p in F_p: the image of omega, from x = u + v*omega_p mod p for eis(x)=(u,v), v!=0."""
    cand = None
    for x in range(2, p):
        u, v = eis(x)
        if v % p != 0:
            wp = (x - u) * pow(v % p, p - 2, p) % p
            if cand is None:
                cand = wp
            else:
                assert cand == wp, f"omega_p inconsistent at p={p}: {cand} vs {wp} (x={x})"
                # one confirmation is enough to be safe; keep checking a few
        if x > 60 and cand is not None:
            break
    # sanity: omega_p is a primitive cube root of 1
    assert (cand * cand + cand + 1) % p == 0, f"omega_p not a cube root at p={p}"
    return cand

def run(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return {'p': p, 'FAIL': 'orientation'}
    wp = omega_p_of(p, eis)
    wp2 = wp * wp % p                                    # omega_p^2

    def tau(x):                                          # the bare conjugation reflection
        u, v = eis(x)
        return (u + v * wp2) % p
    betapow = [1, beta % p, beta * beta % p]

    # the 6 reflection-type maps R_k(x) = beta^k * tau(x)
    results = []
    for k in range(3):                                   # beta has order 3; -1 gives the other 3
        for sgn in (1, -1):
            def Rk(x, k=k, sgn=sgn):
                return (sgn * betapow[k] * tau(x)) % p
            flips_sigma = all(sig(Rk(x)) == -sig(x) for x in range(1, p))
            keeps_chi2 = all(chi2(Rk(x)) == chi2(x) for x in range(1, p))
            flips_sc = all(sig(Rk(x)) * chi2(Rk(x)) == -(sig(x) * chi2(x)) for x in range(1, p))
            is_inv = all(Rk(Rk(x)) == x % p for x in range(1, p))
            results.append({'k': k, 'sgn': sgn, 'flips_sigma': flips_sigma,
                            'keeps_chi2': keeps_chi2, 'flips_sc': flips_sc, 'is_inv': is_inv})
    # is tau itself an involution / multiplicative?
    tau_inv = all(tau(tau(x)) == x % p for x in range(1, p))
    # multiplicative test: tau(x)/x constant?
    ratios = set((tau(x) * pow(x, p - 2, p)) % p for x in range(1, p) if x % p)
    tau_mult = len(ratios) == 1
    FLD = sum(sig(x) * chi2(x) for x in range(p))
    return {'p': p, 'n': n, 'pmod8': p % 8, 'orient': orient, 'FLD': FLD,
            'tau_inv': tau_inv, 'tau_mult': tau_mult, 'refl': results,
            'any_flips_sc': any(r['flips_sc'] for r in results)}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 1300
    print(f"# Reflection-symmetry hunt for the S conservation, p in [{lo},{hi}), p=1 mod 6, n prime.")
    print(f"# tau = conjugation (omega->omega^2 in the rhombus). R_k = beta^k * (+-1) * tau.")
    print(f"# {'p':>6} {'m8':>3} {'FLD':>5} {'tau_inv':>7} {'tau_mult':>8} "
          f"{'any R flips sigma*chi2':>22} {'which':>18}")
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = run(p)
        if r is None or 'FAIL' in (r or {}):
            if r and 'FAIL' in r: print(f"  {p:>6}  FAIL {r['FAIL']}")
            continue
        which = [(rr['k'], rr['sgn']) for rr in r['refl'] if rr['flips_sc']]
        # also: does any reflection flip sigma AND keep chi2 (the clean mechanism)?
        clean = [(rr['k'], rr['sgn']) for rr in r['refl'] if rr['flips_sigma'] and rr['keeps_chi2']]
        print(f"  {p:>6} {r['pmod8']:>3} {r['FLD']:>5} {str(r['tau_inv']):>7} {str(r['tau_mult']):>8} "
              f"{str(r['any_flips_sc']):>22} {str(which):>18}")
    print()
    print("KILL-CONDITION: a reflection R with sigma*chi2(Rx) = -sigma*chi2(x) for ALL x would force")
    print("S=0 by pairing flap orbits with opposite sign. If the 'any R flips sigma*chi2' column is")
    print("False everywhere, the reflection candidate is KILLED like the multiplicative one was.")

if __name__ == '__main__':
    main()
