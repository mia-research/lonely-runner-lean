#!/usr/bin/env sage
# OOS test of the refined rule at p=163 (3 mod 4, leg=-1) => PREDICTED branch 1, eps=-1.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core
p = 163; n = core.curve_order(p); leg = 1 if p % 4 == 1 else -1
K = CyclotomicField(12*n); z = K.gen(); z3 = z**(4*n)
Kn = CyclotomicField(n); zn = Kn.gen(); phi = Kn.hom([z**12], K)
R = PolynomialRing(K, 'T'); T = R.gen()
dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
print(f"p={p} n={n} deg(K)={K.degree()} leg={leg:+d} | PREDICTED branch=1, eps=-1", flush=True)
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
    g1, g2 = sorted(facs, key=lambda f: tuple(tuple(c.vector()) for c in f.list()))
    u1, u2 = g1[0], g2[0]
    eps = next((e for e in (1, -1) if {u1, u2} == {e*p*z3, e*p*z3**2}), None)
    br = 1 if T**2 - z3*(-g1[1])*T + z3**2*u1 == g2 else 2
    print(f"  a={a}: MEASURED branch={br} eps={eps} | u1*u2==p^2 ? {u1*u2 == K(p**2)} "
          f"| PREDICTION {'CONFIRMED' if (br == 1 and eps == -1) else 'REFUTED'} [{time.time()-t0:.0f}s]", flush=True)  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
    done += 1
    if done == 2: break
