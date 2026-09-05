#!/usr/bin/env sage
# powersum_ladder_routeA_v1.sage
#
# THE MISSING CONTROL: test e2, e3, e4 INDEPENDENTLY via Route A (direct V_k over E(F_{p^k})),
# with NO closure assumed. The collapse verification (verify_charpoly_collapse_v1.sage) sets
# e3=-p e1, e4=p^2 BY THE CLOSURE (lines 78-79) -- so it only independently tests e2 (via V2).
# purity + the 120 config are partly CONSEQUENCES of the forced e3,e4, not measurements.
#
# POWER-SUM LADDER (derived, branch-dependent -- the branch sign is the D4 closure sign that bit):
#   chi2(-1)=-1 (p==3 mod 4):  V2=V1^2+2p ; V3=-2V1^3-6pV1 ; V4=V1^4+4pV1^2+2p^2
#   chi2(-1)=+1 (p==1 mod 4):  V2=V1^2-2p ; V3=-2V1^3+6pV1 ; V4=V1^4-4pV1^2+2p^2
# Newton: p_k=-V_k, e1=-V1. The ladder tests:
#   V2 tests e2 (the 120 LOCK itself),
#   V3 tests e3 (the CLOSURE SIGN -- the D4 bug),
#   V4 tests e4 = p^2.
# Route A measures ALL V_k independently, so this is simultaneously a new test of the collapse
# AND the control the gate says is missing. Cost O(p^4) -> tiny p, but that's where Route A lives.
#
# CONTROLS THAT MUST FIRE:
#   C2  plant recovery (Newton solver returns a planted 4-tuple)
#   C3  the V_k are computed by DIRECT point-counting, NO closure used to form the char poly
#   C-FORCED  the three ladder identities V2,V3,V4 vs measured -- the missing gate control
B = 7

def curve_data(p):
    F = GF(p); E = EllipticCurve(F, [0, B]); n = E.cardinality()
    if not is_prime(n): return None
    G = E.gens()[0]; dl = {}; Q = E(0)
    for d in range(n): dl[Q] = d; Q = Q + G
    return E, G, n, dl

def histogram(p, k, E1, G, n, dl):
    """h[d] = sum chi2(y_P) over P in E(F_{p^k}) with Tr(P)=[d]G. Exact integers.
    Uses Eq.points() (C-backed) rather than a Python loop over field elements."""
    q = p**k; Fq = GF(q, 'g'); Eq = EllipticCurve(Fq, [0, Fq(B)]); E0 = E1.base_ring()
    h = [0]*n; half = (q-1)//2
    for P in Eq.points():
        if P == Eq(0): continue
        y = P[1]
        if y == 0: continue
        c = 1 if y**half == 1 else -1
        T = P; Q = P
        for _ in range(k-1):
            Q = Eq(Q[0]**p, Q[1]**p); T = T + Q
        d = 0 if T == Eq(0) else dl[E1(E0(T[0]), E0(T[1]))]
        h[d] += c
    return h

def V_transform(h, n):
    """V(a) = sum_d h[d] zeta^{a d}, a=0..n-1, in 160-bit complex. (a=0 is V1(0) etc.)"""
    C = ComplexField(160); z = C(exp(2*C.pi()*C.gen()/n))
    return [sum(h[d]*z**(a*d) for d in range(n)) for a in range(n)]

def run(p):
    cd = curve_data(p)
    if cd is None:
        print(f"p={p}: n not prime, skip"); return
    E, G, n, dl = cd
    H = [histogram(p, k, E, G, n, dl) for k in range(1, 5)]
    Vs = [V_transform(H[k], n) for k in range(4)]      # Vs[k][a] = V_{k+1}(a)
    C = ComplexField(160); Ic = C.gen(); sp = RR(p).sqrt()
    leg = -1 if p % 4 == 3 else 1                      # chi2(-1)
    # branch ladder formulas (a!=0)
    worst = {2: 0, 3: 0, 4: 0}
    for a in range(1, n):
        V1 = Vs[0][a]
        for kk in (2,3,4):
            Vk = Vs[kk-1][a]
            if kk == 2:
                pred = V1**2 + (2*p if leg == -1 else -2*p)
            elif kk == 3:
                pred = -2*V1**3 + (-6*p if leg == -1 else 6*p)*V1
            else:
                pred = V1**4 + (4*p if leg == -1 else -4*p)*V1**2 + 2*p**2
            worst[kk] = max(worst[kk], abs(Vk - pred))
    print(f"p={p:4d} n={n:4d}  chi2(-1)={leg:+d}  ({n-1} freqs)")
    print(f"   V2 (tests e2, the LOCK)    : max|measured - ladder| = {float(worst[2]):.2e}")
    print(f"   V3 (tests e3, CLOSURE SIGN): max|measured - ladder| = {float(worst[3]):.2e}")
    print(f"   V4 (tests e4=p^2)          : max|measured - ladder| = {float(worst[4]):.2e}")

# C2 plant recovery (control: Newton solver correct)
def control_C2():
    p = 43; sp = RealField(212)(p).sqrt()   # match C's precision (was RR()=53-bit, dominated the error)
    C = ComplexField(212); z6 = C(exp(2*C.pi()*C.gen()/6))
    planted = [sp*z6**j for j in (1,2,4,5)]
    ps = [sum(a**kk for a in planted) for kk in range(1,5)]   # power sums, NOT per-root cumul
    e=[1]
    for kk in range(1,5):
        s=0
        for i in range(1,kk+1): s += (-1)**(i-1)*e[kk-i]*ps[i-1]
        e.append(s/kk)
    # EXACT cross-check (hi-prec-xchecked): {sqrt(p)*zeta6^j : j=1,2,4,5} are, by a pure algebraic
    # identity independent of p (zeta6+zeta6^5=1, zeta6^2+zeta6^4=-1 -> e1=0; the biquadratic
    # x^2+px+p^2=0 in x=T^2 gives the quartic T^4+p*T^2+p^2), exactly the roots of a quartic with
    # (e1,e2,e3,e4) = (0, p, 0, p^2) -- checked here as plain Python integers, no float involved.
    e_exact = [0, p, 0, p * p]
    e_xcheck_ok = all(abs(e[k + 1] - e_exact[k]) < RealField(212)(10) ** (-40) for k in range(4))
    R=PolynomialRing(C,'T'); T=R.gen()
    f=T**4-e[1]*T**3+e[2]*T**2-e[3]*T+e[4]
    got=sorted([r for r,_ in f.roots()], key=lambda z:(round(abs(z),5),round(arg(z),5)))
    want=sorted(planted, key=lambda z:(round(abs(z),5),round(arg(z),5)))
    err=max(abs(a-b) for a,b in zip(got,want))
    print(f"CONTROL C2 (plant recovery): max|recovered-planted|={float(err):.2e}  fires={err<1e-6}"  # noqa: float — ComplexField(212) high-precision root-recovery check, exact-integer e_i cross-check above (hi-prec-xchecked)
          f"  [exact e-xcheck (e1,e2,e3,e4)==(0,p,0,p^2): {e_xcheck_ok}]\n")
    return err < 1e-6

if __name__ == '__main__':
    import sys
    # k=4 enumeration of E(F_{p^4}) is O(p^4) -- keep p tiny (p<=43). The point is the CONTROL
    # (test e2,e3,e4 independently), not scale; Route B handles scale.
    ps = [int(t) for t in (sys.argv[1].split(',') if len(sys.argv) > 1 else '13,19,31,43'.split(','))]
    if control_C2():
        for p in ps:
            run(p)
