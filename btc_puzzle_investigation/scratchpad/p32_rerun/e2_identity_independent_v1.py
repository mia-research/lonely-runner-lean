"""
INDEPENDENT RE-RUN of P32 / #26: the e2 identity   e2 = e1^2 - chi2(-1)*p
                          equivalently  S2 = -S1^2 + 2*chi2(-1)*p
This is the 'owed isolated re-run' (POSITIVE_FINDINGS_MASTER_v14, AUDIT_ideation_agent_claims).
Written from the STATEMENT only -- no code reused from the original run.

S_k = - sum_{Q in E(F_{p^k})}  chi2^{(k)}(y_Q) * psi_a(Nm_k Q),  Nm_k Q = sum_j Frob^j Q  in E(F_p)
psi_a(R) = zeta_n^{a*dlog(R)}.  S1,S2 live in Z[zeta_n].

EXACT: elements of Z[zeta_n] are length-n integer coefficient vectors; v == 0  iff  all entries equal
(since 1+z+...+z^{n-1}=0, n prime).  No floating point anywhere.

THREE ARMS (the claim under test is 'hypothesis is n ODD, not j=0'):
  A  j=0 curves        (y^2=x^3+B)          -> identity must HOLD
  B  non-j=0, n ODD    (y^2=x^3+Ax+B)       -> identity must HOLD   <-- the surprising claim
  C  n EVEN            (any A,B)            -> FIRING CONTROL: must FAIL
"""
import sys, itertools

def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)

# ---------- E(F_p) ----------
def pts_Fp(p, A, B):
    return [(x, y) for x in range(p) for y in range(p) if (y*y - (x*x*x + A*x + B)) % p == 0]

def add_Fp(P, Q, p, A):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1 == x2 and (y1+y2) % p == 0: return None
    lam = ((3*x1*x1+A) * pow(2*y1, -1, p) if P == Q else (y2-y1) * pow(x2-x1, -1, p)) % p
    x3 = (lam*lam - x1 - x2) % p
    return (x3, (lam*(x1-x3) - y1) % p)

# ---------- F_{p^2} = F_p[t]/(t^2 - r) ----------
def make_F2(p):
    r = next(u for u in range(2, p) if legendre(u, p) == -1)
    return r
def m2(a, b, p, r):  # (a0+a1 t)(b0+b1 t)
    return ((a[0]*b[0] + r*a[1]*b[1]) % p, (a[0]*b[1] + a[1]*b[0]) % p)
def s2(a, b, p): return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)
def n2(a, p):    return ((-a[0]) % p, (-a[1]) % p)
def inv2(a, p, r):
    d = pow((a[0]*a[0] - r*a[1]*a[1]) % p, -1, p)
    return (a[0]*d % p, (-a[1]) * d % p)
def pow2(a, e, p, r):
    R = (1, 0)
    while e:
        if e & 1: R = m2(R, a, p, r)
        a = m2(a, a, p, r); e >>= 1
    return R
def pts_F2(p, A, B, r):
    sq = {}                                   # y^2 -> [y, ...]   (O(p^2) instead of O(p^4))
    for y0 in range(p):
        for y1 in range(p):
            sq.setdefault(m2((y0, y1), (y0, y1), p, r), []).append((y0, y1))
    out = []
    for x0 in range(p):
        for x1 in range(p):
            x = (x0, x1)
            x3 = m2(m2(x, x, p, r), x, p, r)
            rhs = s2(s2(x3, (A*x0 % p, A*x1 % p), p), (B, 0), p)
            for y in sq.get(rhs, ()):
                out.append((x, y))
    return out
def add_F2(P, Q, p, A, r):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1 == x2 and s2(y1, y2, p) == (0, 0): return None
    if P == Q:
        num = s2((3*m2(x1,x1,p,r)[0] % p, 3*m2(x1,x1,p,r)[1] % p), (A, 0), p)
        den = (2*y1[0] % p, 2*y1[1] % p)
    else:
        num = s2(y2, n2(y1, p), p); den = s2(x2, n2(x1, p), p)
    lam = m2(num, inv2(den, p, r), p, r)
    x3 = s2(s2(m2(lam, lam, p, r), n2(x1, p), p), n2(x2, p), p)
    y3 = s2(m2(lam, s2(x1, n2(x3, p), p), p, r), n2(y1, p), p)
    return (x3, y3)
def frob2(P, p):
    if P is None: return None
    (x0,x1),(y0,y1) = P
    return ((x0, (-x1) % p), (y0, (-y1) % p))   # t^p = -t since t^2=r, r a non-residue

# ---------- Z[zeta_n] as length-n integer vectors ----------
def zz_zero(v):            # v == 0 in Z[zeta_n]  <=>  all coefficients equal
    return len(set(v)) <= 1
def zz_mul(u, v, n):
    w = [0]*n
    for i, ui in enumerate(u):
        if ui:
            for j, vj in enumerate(v):
                if vj: w[(i+j) % n] += ui*vj
    return w

def run(p, A, B, label, expect):
    P0 = pts_Fp(p, A, B)
    n = len(P0) + 1
    G = None
    for cand in P0:                                  # find a generator
        T = cand; k = 1
        while T is not None:
            T = add_Fp(T, cand, p, A); k += 1
        if k == n: G = cand; break
    if G is None: return (label, p, A, B, n, "SKIP: no generator (non-cyclic)", None)
    dlog = {}; T = G
    for k in range(1, n):
        dlog[T] = k; T = add_Fp(T, G, p, A)
    dlog_of = lambda R: 0 if R is None else dlog[R]

    r = make_F2(p)
    P2 = pts_F2(p, A, B, r)
    chi = legendre(-1, p)
    E2EXP2 = (p*p - 1)//2
    results = []
    for a in range(1, n):
        S1 = [0]*n
        for (x, y) in P0:
            c = legendre(y, p)
            if c: S1[(a*dlog[(x, y)]) % n] -= c        # S1 = -sum ...
        S2 = [0]*n
        for Q in P2:
            y = Q[1]
            if y == (0, 0): continue
            c = 1 if pow2(y, E2EXP2, p, r) == (1, 0) else -1
            Nm = add_F2(Q, frob2(Q, p), p, A, r)       # Q + Frob Q  (lands in E(F_p))
            R = None if Nm is None else (Nm[0][0], Nm[1][0])
            assert Nm is None or (Nm[0][1] == 0 and Nm[1][1] == 0), "norm not F_p-rational"
            S2[(a*dlog_of(R)) % n] -= c
        # test  S2 + S1^2 - 2*chi*p == 0
        lhs = zz_mul(S1, S1, n)
        for i in range(n): lhs[i] += S2[i]
        lhs[0] -= 2*chi*p
        results.append(zz_zero(lhs))
    ok = all(results)
    return (label, p, A, B, n, f"{sum(results)}/{len(results)} cells hold", ok)

if __name__ == "__main__":
    ARMS = [
        # ARM A -- j=0, n odd
        ("A j=0   ", [(11,0,4),(11,0,7),(13,0,1),(17,0,2),(19,0,3),(23,0,5)]),
        # ARM B -- non-j=0 (A != 0), n odd  <-- the surprising generality claim
        ("B nonj0 ", [(11,1,1),(13,2,3),(17,1,5),(19,3,1),(23,1,4),(29,2,1),(31,5,2)]),
        # ARM C -- n EVEN: FIRING CONTROL, identity must FAIL
        ("C even-n", [(11,1,6),(13,1,1),(17,2,2),(19,1,2),(23,3,3),(29,1,1)]),
    ]
    for label, cases in ARMS:
        for (p, A, B) in cases:
            npts = len(pts_Fp(p, A, B)) + 1
            if (npts % 2 == 0) != (label.startswith("C")):
                continue                                   # keep arms clean by parity
            out = run(p, A, B, label, None)
            print(f"{out[0]} p={p:3d} A={A} B={B}  n={out[4]:3d}  {out[5]}", flush=True)
