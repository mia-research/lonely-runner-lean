#!/usr/bin/env sage
# rho_artifact_probe_v1 — is rho_p intrinsic, or an artifact of canon()'s lex rule?
#
# HYPOTHESIS (pre-registered, this file written before any run):
#   Write the two [2,2] factors g1 = T^2 - s1 T + u1, g2 = T^2 - s2 T + u2 with
#   s2 = rho s1, u2 = rho^2 u1 (brick 2).  Then u1 u2 = e4 = p^2 forces
#       (u1 rho)^2 = p^2  =>  u1 = eps p rho^-1,  u2 = eps p rho
#   so the SET {u1,u2} = {eps p z3, eps p z3^2} for EVERY cell a, with eps = +-1 the
#   only free quantity.  canon() sorts on f.list() = [u, -s, 1], constant coeff FIRST,
#   and u1 != u2 always => the sort NEVER reaches the T-coefficient.  Hence:
#     (i) if eps is a-independent, the branch is FORCED constant across cells
#         (global constancy is not evidence of rigidity);
#     (ii) the branch VALUE is a function of n = #E(F_p) alone, via the power-basis
#          coordinate vectors of z3, z3^2 in Q(zeta_{12n}) -- no arithmetic of p.
#
# PREDICTION RULE:  branch = 1  <=>  vec(eps*p*z3^2) <lex vec(eps*p*z3).
#   (lex-min factor is g1; branch=1 means u2 = z3^2 u1, i.e. u1 = eps p z3^2.)
#
# FALSIFIER: if this rule does not reproduce the observed {43:1, 61:2, 79:1},
#   the deflation is WRONG and rho_p survives as a genuine invariant.
#
# ARM C (out-of-sample): predict p=163 before the in-flight brick1 job prints it.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

OBSERVED = {43: 1, 61: 2, 79: 1}

def canon_key(f):
    return tuple(tuple(c.vector()) for c in f.list())

def predict(p, n, eps):
    K = CyclotomicField(12*n); z = K.gen(); z3 = z**(4*n)
    vA = tuple((eps*p*z3).vector())      # candidate u = eps p z3
    vB = tuple((eps*p*z3**2).vector())   # candidate u = eps p z3^2
    return 1 if vB < vA else 2

# ---- ARM A: prediction from n alone, both signs of eps ----
print("ARM A — branch predicted from n alone (no curve data beyond n):", flush=True)
ns = {}
for p in (43, 61, 79, 163):
    t0 = time.time()  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
    n = core.curve_order(p); ns[p] = n
    pm = predict(p, n, -1); pp = predict(p, n, +1)
    obs = OBSERVED.get(p, "?")
    print(f"  p={p:4d}  n={n:4d}  pred(eps=-1)={pm}  pred(eps=+1)={pp}  observed={obs}  [{time.time()-t0:.0f}s]", flush=True)  # noqa: float — (display) elapsed-time logging only, never fed back into any decision

print(flush=True)
for eps in (-1, 1):
    hits = sum(1 for p in OBSERVED if predict(p, ns[p], eps) == OBSERVED[p])
    print(f"  eps={eps:+d}: reproduces {hits}/3 observed branches", flush=True)

# ---- ARM B: direct check of the u-structure at p=43 (3 cells) ----
print("\nARM B — actual (u1,u2) at p=43, first 3 coprime cells:", flush=True)
p = 43; n = ns[43]
K = CyclotomicField(12*n); z = K.gen(); z3 = z**(4*n)
Kn = CyclotomicField(n); zn = Kn.gen()
phi = Kn.hom([z**12], K)
R = PolynomialRing(K, 'T'); T = R.gen()
dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
done = 0
for a in range(1, n):
    if gcd(a, n) != 1: continue
    V1 = sum(h1[d]*zn**((a*d) % n) for d in range(n))
    V2 = sum(h2[d]*zn**((a*d) % n) for d in range(n))
    leg = 1 if p % 4 == 1 else -1
    e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = Kn(p**2)  # noqa: float — exact division by 2 in the cyclotomic field Q(zeta_n) (Sage exact ring, not IEEE); mirrors build_L in lmono_brick1_branch_v2.sage
    L = T**4 - phi(e1)*T**3 + phi(e2)*T**2 - phi(e3)*T + phi(e4)
    facs = [f for f, e in L.factor()]
    if sorted(f.degree() for f in facs) != [2, 2]:
        print(f"  a={a}: not [2,2]"); continue
    g1, g2 = sorted(facs, key=canon_key)
    u1, u2 = g1[0], g2[0]
    br = 1 if T**2 - z3*(-g1[1])*T + z3**2*u1 == g2 else 2
    print(f"  a={a}: u1 == -p*z3^2 ? {u1 == -p*z3**2} | u1 == -p*z3 ? {u1 == -p*z3} | "
          f"u2 == -p*z3 ? {u2 == -p*z3} | u2 == -p*z3^2 ? {u2 == -p*z3**2} | "
          f"u1*u2 == p^2 ? {u1*u2 == K(p**2)} | u1 != u2 ? {u1 != u2} | branch={br}", flush=True)
    done += 1
    if done == 3: break
