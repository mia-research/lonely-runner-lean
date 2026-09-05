#!/usr/bin/env sage
# brick2_identity_v1 — reduce T2/brick-2 to an elementary identity and test it at scale.
#
# DERIVATION (above): roots(L*) = S u rho*S with rho^3=1 forces, given e3=leg*p*e1, e4=p^2:
#     e3^2 = e4*e1^2   (AUTOMATIC -- carries no information)
#     e2 = e1^2 - leg*p   <=>   V2 = V1^2 - 2*leg*p    (the ONLY non-automatic condition)
# So brick 2's exact rescaling, verified at 7 cells by degree-240..792 factorisations,
# should be equivalent to a Q(zeta_n) identity computable in milliseconds.
#
# ARM 1: test V2 == V1^2 - 2*leg*p at EVERY cell of several primes (exact, no factorisation).
# ARM 2: confirm e3^2 == e4*e1^2 is identically automatic (it must be).
# ARM 3: decomposition-group test -- is u1 in p*mu FORCED by purity?  Purity + CM gives
#        u1*c(u1) = p^2; u1/p is an algebraic integer iff complex conjugation lies in the
#        decomposition group at p, i.e. iff -1 is in <p> mod 12n.  If that FAILS somewhere,
#        u1 in p*mu is a genuine measured fact, not a forced one.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

print("ARM 3 — is complex conjugation in the decomposition group at p?  (-1 in <p> mod 12n)", flush=True)
for p in (43, 61, 67, 79, 97, 103, 127, 139, 151, 163, 211):
    n = core.curve_order(p); m = 12*n
    if gcd(p, m) != 1:
        print(f"  p={p:4d} n={n:4d}: p | 12n  (p ramifies/divides the conductor) — test N/A", flush=True); continue
    g = Integers(m)(p); orb = set()
    x = Integers(m)(1)
    for _ in range(m):
        x *= g; orb.add(x)
        if x == 1: break
    inn = (Integers(m)(-1) in orb)
    print(f"  p={p:4d} n={n:4d} m={m:5d}: ord(p mod m)={len(orb):4d}  -1 in <p> ? {inn}", flush=True)

print("\nARM 1 + 2 — the identity at every cell:", flush=True)
for p in (43, 61, 67, 79, 97, 103, 127, 139, 151, 163):
    t0 = time.time()  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
    n = core.curve_order(p); leg = 1 if p % 4 == 1 else -1
    Kn = CyclotomicField(n); zn = Kn.gen()
    dl = core.dlog_table(p, n); h1 = core.hist_k1(p, n, dl); h2 = core.hist_k2(p, n, dl)
    ok1 = ok2 = tot = 0; bad = []
    for a in range(1, n):
        if gcd(a, n) != 1: continue
        V1 = sum(h1[d]*zn**((a*d) % n) for d in range(n))
        V2 = sum(h2[d]*zn**((a*d) % n) for d in range(n))
        e1 = -V1; e2 = (V1**2 + V2)/2; e3 = leg*p*e1; e4 = Kn(p**2)  # noqa: float — exact division by 2 in the cyclotomic field Q(zeta_n) (Sage exact ring, not IEEE); mirrors build_L in lmono_brick1_branch_v2.sage
        tot += 1
        if V2 == V1**2 - 2*leg*p: ok1 += 1
        else: bad.append(a)
        if e3**2 == e4*e1**2: ok2 += 1
    print(f"  p={p:4d} n={n:4d} leg={leg:+d}: identity V2==V1^2-2*leg*p  {ok1}/{tot} cells | "
          f"e3^2==e4*e1^2 {ok2}/{tot} | {'ALL PASS' if ok1==tot else f'FAIL at a={bad[:6]}'} "
          f"[{time.time()-t0:.0f}s]", flush=True)  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
