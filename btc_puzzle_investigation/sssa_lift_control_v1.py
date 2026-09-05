#!/usr/bin/env python3
"""
INITIAL INSTRUMENT VALIDATION (mechanical layer only) for the representation-boundary
program.  NOT the leakage test.  Establishes:

  (1) FIRING CONTROL: SSSA p-adic-lift attack recovers d EXACTLY on an anomalous
      curve (#E = p).  This is the "does the plant fire" check.
  (2) NEGATIVE BASELINE: on a non-anomalous CM curve y^2=x^3+7 (n != p), the SAME
      machinery does NOT recover d, and the recovered value DEPENDS ON THE LIFT K
      (differs when we lift with x~ vs x~+p).  This is the mechanical witness of the
      circularity located in PLAN_representation_boundary_program_v1.md sec 3:
      n a p-adic unit => the free lift term enters d at leading order.

Exact integer arithmetic only (mod p^N).  No floats in the signal path.
Homogeneous (Washington) projective coords: z_formal = -X/Y needs Y a unit (it is),
never divides by Z, so the E_1 point (Z ~ 0 mod p) is represented without blow-up.
"""
import random

def inv(a, m): return pow(a % m, -1, m)

# ---------- homogeneous projective EC arithmetic over Z/m (Washington) ----------
def is_unit(z, p, m): return z % p != 0

def normalize(P, p, m):
    if P is None: return None
    X, Y, Z = P
    if Z % p != 0:                      # Z unit -> affine (x,y,1)
        zi = inv(Z, m); return (X*zi % m, Y*zi % m, 1)
    return (X % m, Y % m, Z % m)        # E_1 / near-O point: leave as is

def dbl(P, a, m):
    X1, Y1, Z1 = P
    t = (a*Z1*Z1 + 3*X1*X1) % m
    u = (Y1*Z1) % m
    v = (u*X1*Y1) % m
    w = (t*t - 8*v) % m
    X3 = (2*u*w) % m
    Y3 = (t*(4*v - w) - 8*Y1*Y1*u*u) % m
    Z3 = (8*u*u*u) % m
    return (X3, Y3, Z3)

def add_raw(P, Q, a, m):
    X1, Y1, Z1 = P; X2, Y2, Z2 = Q
    u = (Y2*Z1 - Y1*Z2) % m
    v = (X2*Z1 - X1*Z2) % m
    w = (u*u*Z1*Z2 - v*v*v - 2*v*v*X1*Z2) % m
    X3 = (v*w) % m
    Y3 = (u*(v*v*X1*Z2 - w) - v*v*v*Y1*Z2) % m
    Z3 = (v*v*v*Z1*Z2) % m
    return (X3, Y3, Z3)

def add(P, Q, a, m, p):
    if P is None: return Q
    if Q is None: return P
    Pn = normalize(P, p, m); Qn = normalize(Q, p, m)
    # both finite (Z unit) during the whole scalar-mult chain except the final output
    if Pn[2] % p != 0 and Qn[2] % p != 0:
        if Pn[0] == Qn[0]:                       # same x
            if Pn[1] == Qn[1]: return dbl(Pn, a, m)
            else: return None                     # inverse -> O
    return add_raw(Pn, Qn, a, m)

def mul(k, P, a, m, p):
    R = None; base = P
    while k:
        if k & 1: R = add(R, base, a, m, p)
        base = dbl(normalize(base, p, m), a, m)
        k >>= 1
    return R

# ---------- point counting on y^2=x^3+ax+b over F_p ----------
def count_points(a, b, p):
    cnt = 1  # O
    for x in range(p):
        rhs = (x*x*x + a*x + b) % p
        cnt += 1 + pow(rhs, (p-1)//2, p) if rhs != 0 else 1
        # legendre: 1 + chi(rhs); chi(0)=0 -> 1 pt
        if rhs != 0:
            cnt -= 1  # correct the +1 above; recompute cleanly below
    # clean recompute (avoid the messy inline)
    cnt = 1
    for x in range(p):
        rhs = (x*x*x + a*x + b) % p
        if rhs == 0: cnt += 1
        else:
            ls = pow(rhs, (p-1)//2, p)
            cnt += 2 if ls == 1 else 0
    return cnt

def find_pt(a, b, p):
    for x in range(1, p):
        rhs = (x*x*x + a*x + b) % p
        if rhs == 0: continue
        if pow(rhs, (p-1)//2, p) == 1:
            for y in range(1, p):
                if (y*y) % p == rhs: return (x, y)
    return None

def hensel_y(x_lift, a, b, p, N):
    m = p**N
    rhs = (x_lift**3 + a*x_lift + b) % m
    # start from y0 with y0^2 = rhs mod p
    r0 = rhs % p
    y = next(y for y in range(p) if (y*y) % p == r0)
    for _ in range(N+2):                          # Newton lift: y <- y - f/f'
        f = (y*y - rhs) % m
        fp = (2*y) % m
        y = (y - f*inv(fp, m)) % m
    assert (y*y - rhs) % m == 0
    return y

def z_formal(R, p, m):
    """ -X/Y for an E_1 point (Y unit); returns value in pZ/mZ """
    X, Y, Z = R
    return (-X * inv(Y, m)) % m

def pval(x, p, N):
    if x % (p**N) == 0: return N
    v = 0
    while x % p == 0: x //= p; v += 1
    return v

def recover_d(P_aff, Q_aff, a, b, p, order, N, dxP=0, dxQ=0):
    """SSSA: lift, multiply by `order` to land in E_1, d = z(orderQ)/z(orderP) mod p.
    Valuation-robust: read the FIRST nonzero p-adic digit of each z; require equal
    valuation (else the elliptic-log hom degenerates and we return None)."""
    m = p**N
    xP, yP = P_aff; xQ, yQ = Q_aff
    xPl = xP + dxP; xQl = xQ + dxQ
    Pt = (xPl % m, hensel_y(xPl, a, b, p, N), 1)
    Qt = (xQl % m, hensel_y(xQl, a, b, p, N), 1)
    RP = mul(order, Pt, a, m, p)
    RQ = mul(order, Qt, a, m, p)
    zP = z_formal(RP, p, m); zQ = z_formal(RQ, p, m)
    assert zP % p == 0 and zQ % p == 0, "order*P not in E_1 (Z not ~0 mod p)"
    vP = pval(zP, p, N); vQ = pval(zQ, p, N)
    if vP != vQ or vP >= N: return None
    aP = (zP // p**vP) % p; aQ = (zQ // p**vQ) % p
    if aP % p == 0: return None
    return (aQ * inv(aP, p)) % p

# ================================================================
random.seed(20260813)
N = 4

print("="*70)
print("(1) FIRING CONTROL  — anomalous curve  #E(F_p) = p")
print("="*70)
anom = None
for p in [q for q in range(37, 400) if all(q % d for d in range(2, int(q**.5)+1))]:
    for a in range(1, 9):                # a != 0 -> generic j (avoid j=0 CM, lambda=0)
        for b in range(1, 9):
            if (4*a**3 + 27*b**2) % p == 0: continue
            if count_points(a, b, p) == p:
                anom = (p, a, b); break
        if anom: break
    if anom: break
p, a, b = anom
G = find_pt(a, b, p)
print(f"curve y^2 = x^3 + {a}x + {b}  over F_{p}   #E = {count_points(a,b,p)} = p (anomalous)")
print(f"generator G = {G}")
def resolve_sign(v, G, Qa, a, p):
    """v = +/-d mod p; pick the sign by the public check [v]G == Q (x,y)."""
    if v is None: return None
    R = normalize(mul(v % p, (G[0], G[1], 1), a, p, p), p, p)
    if R is not None and (R[0], R[1]) == Qa: return v % p
    return (-v) % p

ok = 0; trials = 8
for _ in range(trials):
    d = random.randrange(1, p)
    Q = mul(d, (G[0], G[1], 1), a, p, p); Q = normalize(Q, p, p); Qa = (Q[0], Q[1])
    dr = resolve_sign(recover_d(G, Qa, a, b, p, p, N), G, Qa, a, p)
    dr2 = resolve_sign(recover_d(G, Qa, a, b, p, p, N, dxQ=p), G, Qa, a, p)  # lift x+p
    tag = "OK" if dr == d else "FAIL"
    same = "lift-invariant" if dr == dr2 else "lift-DEPENDENT"
    print(f"  d={d:3d}  recovered={dr}  (2nd lift={dr2}, {same})  [{tag}]")
    ok += (dr == d)
print(f"\n  FIRING CONTROL: {ok}/{trials} exact recoveries  -> {'FIRES' if ok==trials else 'BROKEN'}")

print("\n" + "="*70)
print("(2) NEGATIVE BASELINE — non-anomalous CM curve  y^2 = x^3 + 7  (n != p)")
print("="*70)
# smallest p = 1 mod 3 with 7 a nonzero, curve nonsingular, and n != p
for p in [q for q in range(11, 200) if all(q % d for d in range(2, int(q**.5)+1)) and q % 3 == 1]:
    a2, b2 = 0, 7
    if (4*a2**3 + 27*b2**2) % p == 0: continue
    n = count_points(a2, b2, p)
    if n == p: continue
    G2 = find_pt(a2, b2, p)
    if G2 is None: continue
    # need G2 of order n (n prime) or just use it; check order
    if n < 5: continue
    break
print(f"curve y^2 = x^3 + 7  over F_{p}   #E = n = {n}  (n != p: {n} != {p})")
print(f"base point G = {G2}")
# use a point of full order if n prime; else fall back to G2
def order_of(P, a, m, p, bound):
    R = None
    for k in range(1, bound+1):
        R = add(R, P, a, m, p)
        if R is None: return k
    return None
ordG = order_of((G2[0], G2[1], 1), a2, p, p, n)
print(f"order(G) = {ordG}")
print("\n  Running SSSA machinery with `order` = n (multiply by n to reach E_1):")
print("  For n != p the recovered value should be WRONG and LIFT-DEPENDENT.\n")
mism = 0; lift_dep = 0; trials2 = 8
for _ in range(trials2):
    d = random.randrange(1, ordG)
    Q = mul(d, (G2[0], G2[1], 1), a2, p, p); Q = normalize(Q, p, p); Qa = (Q[0], Q[1])
    try:
        dr = recover_d(G2, Qa, a2, b2, p, n, N)
        dr2 = recover_d(G2, Qa, a2, b2, p, n, N, dxQ=p)
    except AssertionError as e:
        print(f"  d={d:3d}  [machinery assert: {e}]"); continue
    hit = (dr is not None and dr % ordG == d % ordG)
    same = (dr == dr2)
    mism += (not hit); lift_dep += (not same)
    print(f"  d={d:3d}  'recovered'={dr}  2nd-lift={dr2}  "
          f"{'MATCH' if hit else 'wrong'}  {'lift-invariant' if same else 'lift-DEPENDENT'}")
print(f"\n  BASELINE: {mism}/{trials2} do NOT recover d;  {lift_dep}/{trials2} are lift-dependent.")
print("  => the carry is entangled with the free lift K when n != p (mechanical witness).")
