#!/usr/bin/env sage
# rho_artifact_probe_v2 — refine after v1's rule was FALSIFIED at p=61.
#
# v1 established (ARM B, exact, p=43): {u1,u2} = {eps*p*z3^2, eps*p*z3} with eps = -1,
# u1*u2 = p^2, u1 != u2 => canon() never reads past the constant coefficient.
# v1's uniform-eps rule predicted 1/1/1 but 61 is observed 2.  => eps is NOT uniform.
#
# REFINED HYPOTHESIS: eps = leg = (-1)^((p-1)/2), entering via e3 = leg*p*e1 in build_L.
#   p = 3 mod 4 (leg=-1): roots {a, z3 a, -abar, -z3bar abar} -> u = -p*z3^{-+1}
#   p = 1 mod 4 (leg=+1): roots {a, z3 a,  abar,  z3bar abar} -> u = +p*z3^{-+1}
# Since vec(-v) = -vec(v) reverses lex at the first differing coordinate,
#   branch(eps=+1) = 3 - branch(eps=-1)  identically.
# ARM D tests whether F(n) := branch(eps=-1) is constant in n (making the branch a
# pure function of p mod 4) or genuinely n-dependent.
#
# ARM B2 (the crux): measure eps DIRECTLY at p=61 (leg=+1) and p=79 (leg=-1).
# ARM E (out-of-sample, PRE-REGISTERED): p=163 == 3 mod 4 => predicted branch 1.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

def canon_key(f):
    return tuple(tuple(c.vector()) for c in f.list())

def F(n):
    """branch predicted under eps=-1, from n alone."""
    K = CyclotomicField(12*n); z = K.gen(); z3 = z**(4*n)
    return 1 if tuple((-z3**2).vector()) < tuple((-z3).vector()) else 2

# ---- ARM D: is F(n) constant in n? ----
print("ARM D — F(n) over curve orders n = #E(F_p), y^2=x^3+7:", flush=True)
vals = {}
for p in (43, 61, 67, 79, 97, 103, 127, 139, 151, 163, 181, 193, 211, 223, 241, 271, 307, 331, 349):
    n = core.curve_order(p)
    vals[p] = (n, F(n))
print("  " + "  ".join(f"p{p}:n{n}:F{f}" for p, (n, f) in vals.items()), flush=True)
print(f"  distinct F values: {sorted(set(f for _, f in vals.values()))}", flush=True)

# ---- ARM B2: measure eps directly at p=61 (leg=+1) and p=79 (leg=-1) ----
for p in (61, 79):
    n = core.curve_order(p)
    K = CyclotomicField(12*n); z = K.gen(); z3 = z**(4*n)
    Kn = CyclotomicField(n); zn = Kn.gen()
    phi = Kn.hom([z**12], K)
    R = PolynomialRing(K, 'T'); T = R.gen()
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    leg = 1 if p % 4 == 1 else -1
    print(f"\nARM B2 — p={p} (n={n}, leg={leg:+d}), first 3 coprime cells:", flush=True)
    done = 0
    for a in range(1, n):
        if gcd(a, n) != 1: continue
        t0 = time.time()  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
        V1 = sum(h1[d]*zn**((a*d) % n) for d in range(n))
        V2 = sum(h2[d]*zn**((a*d) % n) for d in range(n))
        e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = Kn(p**2)  # noqa: float — exact division by 2 in the cyclotomic field Q(zeta_n) (Sage exact ring, not IEEE); mirrors build_L in lmono_brick1_branch_v2.sage
        L = T**4 - phi(e1)*T**3 + phi(e2)*T**2 - phi(e3)*T + phi(e4)
        facs = [f for f, e in L.factor()]
        if sorted(f.degree() for f in facs) != [2, 2]:
            print(f"  a={a}: not [2,2]", flush=True); continue
        g1, g2 = sorted(facs, key=canon_key)
        u1, u2 = g1[0], g2[0]
        eps = None
        for e in (1, -1):
            if {u1, u2} == {e*p*z3, e*p*z3**2}: eps = e
        br = 1 if T**2 - z3*(-g1[1])*T + z3**2*u1 == g2 else 2
        print(f"  a={a}: measured eps={eps}  (eps==leg ? {eps == leg})  "
              f"u1*u2==p^2 ? {u1*u2 == K(p**2)}  branch={br}  [{time.time()-t0:.0f}s]", flush=True)  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
        done += 1
        if done == 3: break

print("\nARM E — PRE-REGISTERED out-of-sample: p=163 is 3 mod 4 (leg=-1) => predicted branch 1.", flush=True)
