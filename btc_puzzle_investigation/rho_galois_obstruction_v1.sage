#!/usr/bin/env sage
# rho_galois_obstruction_v1 — is a convention-free labeling of the two planes even POSSIBLE?
#
# CLAIM (to test, not assume): L*(a) has coefficients in Q(zeta_n); it splits [2,2] over
# K = Q(zeta_{12n}).  Gal(K/Q(zeta_n)) = {z -> z^j : j = 1 mod n, j in (Z/12)*} has order 4.
# If some sigma in that group SWAPS g1 and g2, then no Q(zeta_n)-rational rule can label
# them -- rho_p is not merely un-canonicalised, it is structurally un-canonicalisable from
# the L-polynomial data alone.
#
# Further: applying sigma to roots(g2) = rho*roots(g1) forces sigma(rho) = rho^-1 for every
# swapping sigma.  So PREDICTED: the stabiliser of each factor is exactly the subgroup
# fixing zeta_3, i.e. j = 1 mod 12 and j = 7 mod 12; the swappers are j = 5, 11 mod 12.
# FALSIFIER: any factor fixed by j=5 or 11, or swapped by j=7.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

p = 43; n = core.curve_order(p); m = 12*n
K = CyclotomicField(m); z = K.gen(); z3 = z**(4*n)
Kn = CyclotomicField(n); zn = Kn.gen(); phi = Kn.hom([z**12], K)
R = PolynomialRing(K, 'T'); T = R.gen()
dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
leg = 1 if p % 4 == 1 else -1

# the four j with j = 1 mod n, j in (Z/12)*
js = [j for j in range(1, m) if gcd(j, m) == 1 and j % n == 1 and j % 12 in (1, 5, 7, 11)]
print(f"p={p} n={n} m={m} deg(K)={K.degree()}")
print(f"Gal(K/Q(zeta_n)) reps j = {js}  (j mod 12 = {[j % 12 for j in js]})", flush=True)
for j in js:
    print(f"   j={j:5d} (j mod 12 = {j % 12:2d}): fixes zeta_n ? {(z**j)**12 == z**12}, "
          f"zeta_3 -> zeta_3^{j % 3}", flush=True)

def sig(f, j):
    return sum(sum(c*z**((e*j) % m) for e, c in zip(range(K.degree()), cc.vector()) if c)
               * T**i for i, cc in enumerate(f.list()))

print("\nper-cell Galois action on the factor pair:", flush=True)
done = 0
for a in range(1, n):
    if gcd(a, n) != 1: continue
    t0 = time.time()  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
    V1 = sum(h1[d]*zn**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*zn**((a*d) % n) for d in range(n))
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = Kn(p**2)  # noqa: float — exact division by 2 in the cyclotomic field Q(zeta_n) (Sage exact ring, not IEEE); mirrors build_L in lmono_brick1_branch_v2.sage
    L = T**4 - phi(e1)*T**3 + phi(e2)*T**2 - phi(e3)*T + phi(e4)
    facs = [f for f, e in L.factor()]
    if sorted(f.degree() for f in facs) != [2, 2]: continue
    g1, g2 = sorted(facs, key=lambda f: tuple(tuple(c.vector()) for c in f.list()))
    acts = {}
    for j in js:
        s = sig(g1, j)
        acts[j % 12] = "fix" if s == g1 else ("swap" if s == g2 else "OTHER(!)")
    ok = (acts.get(1) == "fix" and acts.get(7) == "fix"
          and acts.get(5) == "swap" and acts.get(11) == "swap")
    print(f"  a={a}: {acts}  prediction {'CONFIRMED' if ok else 'REFUTED'} [{time.time()-t0:.0f}s]", flush=True)  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
    done += 1
    if done == 4: break
