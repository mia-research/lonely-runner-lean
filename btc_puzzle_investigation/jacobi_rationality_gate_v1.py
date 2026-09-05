#!/usr/bin/env python3
"""
jacobi_rationality_gate_v1.py  --  2026-09-01

Exact witness for the single remaining gap of RESULT_jacobi_closed_form_m_law_v4.md
(Brick D2, ROADMAP_REDIRECT_v3):

    J(chi3, chi4) over F_q, q = p^2, p = 3 mod 4
        =  -p   for p = 1 mod 3   (i.e. p = 7 mod 12   <-- secp's class)
        =  +p   for p = 2 mod 3   (i.e. p = 11 mod 12)

graded [EMPIRICAL 12/12] there, "NOT proved here".

This script does two exact things.

(A)  Extends the empirical base far past 12 primes, and does it for ALL FOUR
     choices of the character pair (chi3^a, chi4^b), a in {1,2}, b in {1,3},
     so the value cannot be an artefact of one conjugate choice.
     J is accumulated as an exact vector in Z[zeta_12] = Z[x]/(x^4 - x^2 + 1).
     No floats in the verdict path.

(B)  Tests the DERIVED evaluation of the subfield-trivial quartic Gauss sum

         g(chi4) = p * chi4(x0),   x0 = any nonzero trace-zero element,
         chi4(x0) = +1 if p = 7 mod 8,  -1 if p = 3 mod 8

     which v4 records as "fitted to three primes ... may not be named or used
     in a proof until it is [retested out of sample]".  Here it is a derivation
     (see the companion note), and the two load-bearing discrete steps are
     checked exactly:
        (B1) the nonzero trace-zero elements are exactly ONE coset of F_p^*
        (B2) dlog(x0) = (p+1)/2   mod 4     <=>   chi4(x0) = zeta_4^{(p+1)/2}
     A float cross-check of the Gauss sum itself is reported separately and is
     NOT in the verdict path.

Not a leakage test, sweep, scan or anomaly drill: no statistic, no null, no
target involving d.  CLAUDE.md 2's experiment-designer gate does not apply.
No leakage / ECDLP / keyspace claim.
"""
import cmath, sys

# ---------- Z[zeta_12] = Z[x]/(x^4 - x^2 + 1) ----------
# zeta^k reduced to basis (1, x, x^2, x^3)
Z12 = [
    ( 1, 0, 0, 0), ( 0, 1, 0, 0), ( 0, 0, 1, 0), ( 0, 0, 0, 1),
    (-1, 0, 1, 0), ( 0,-1, 0, 1), (-1, 0, 0, 0), ( 0,-1, 0, 0),
    ( 0, 0,-1, 0), ( 0, 0, 0,-1), ( 1, 0,-1, 0), ( 0, 1, 0,-1),
]

def primes_upto(N):
    s = [True]*(N+1); s[0]=s[1]=False
    for i in range(2,int(N**.5)+1):
        if s[i]:
            for j in range(i*i,N+1,i): s[j]=False
    return [i for i in range(N+1) if s[i]]

def factor(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f

def run(p):
    """F_q = F_p[i], i^2 = -1 (valid since p = 3 mod 4)."""
    q = p*p
    # element (a,b) <-> a + b*i, encoded a*p + b
    def mul(u,v):
        a,b = divmod(u,p); c,d = divmod(v,p)
        return ((a*c - b*d) % p)*p + ((a*d + b*c) % p)
    # generator of F_q^*
    order = q-1
    facs = factor(order)
    one = 1*p + 0          # multiplicative identity 1 + 0i  (encoding a*p+b)
    gen = None
    for a in range(0,p):
        for b in range(0,p):
            e = a*p+b
            if e == 0: continue
            ok = True
            for r in facs:
                # e^(order/r)
                x, k, base = one, order//r, e
                while k:
                    if k & 1: x = mul(x, base)
                    base = mul(base, base); k >>= 1
                if x == one: ok = False; break
            if ok: gen = e; break
        if gen is not None: break
    # discrete log table
    dlog = [None]*(q)
    x = one
    for k in range(order):
        dlog[x] = k
        x = mul(x, gen)
    assert x == one
    assert dlog[one] == 0 and all(dlog[u] is not None for u in range(1,q))

    # (A) Jacobi sums, exact in Z[zeta_12]
    results = {}
    for a in (1,2):          # chi3^a
        for b in (1,3):      # chi4^b
            acc = [0,0,0,0]
            for u in range(1, q):        # u = t, encoded; skip t=0
                a1,b1 = divmod(u,p)
                # 1 - t
                w = ((1-a1) % p)*p + ((-b1) % p)
                if w == 0: continue      # t = 1
                e = (4*a*dlog[u] + 3*b*dlog[w]) % 12
                v = Z12[e]
                acc[0]+=v[0]; acc[1]+=v[1]; acc[2]+=v[2]; acc[3]+=v[3]
            results[(a,b)] = tuple(acc)

    # (B1) nonzero trace-zero set = one coset of F_p^*   (Tr(a+bi) = 2a)
    tz = [u for u in range(1,q) if u//p == 0]
    b1_ok = (len(tz) == p-1)
    x0 = tz[0]
    # coset check: every trace-zero elt is x0 * (elt of F_p^*)
    fp_star = set((c % p)*p + 0 for c in range(1,p))
    b1_ok = b1_ok and all(mul(x0, c) in set(tz) for c in fp_star)
    # (B2) dlog(x0) mod 4  vs  (p+1)/2 mod 4     (well-defined: 4 | p+1)
    d0 = dlog[x0] % 4
    pred = ((p+1)//2) % 4
    b2_ok = (d0 == pred)
    chi4_x0 = 1 if d0 % 4 == 0 else (-1 if d0 % 4 == 2 else None)
    sign_rule = 1 if p % 8 == 7 else -1

    # float cross-check of g(chi4)  (NOT in the verdict path)
    zp = [cmath.exp(2j*cmath.pi*k/p) for k in range(p)]
    z4 = [1, 1j, -1, -1j]
    g4 = 0j
    for u in range(1,q):
        aa = u//p
        g4 += z4[dlog[u] % 4] * zp[(2*aa) % p]
    g4_err = abs(g4 - p*chi4_x0) if chi4_x0 is not None else float('nan')

    return results, b1_ok, b2_ok, chi4_x0, sign_rule, g4_err

def fmt(vec, p):
    if vec == (p,0,0,0):  return "+p"
    if vec == (-p,0,0,0): return "-p"
    return str(vec)

if __name__ == "__main__":
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    ps = [p for p in primes_upto(LIM) if p % 4 == 3 and p > 3]
    print(f"p<={LIM}, p=3 mod 4 : {len(ps)} primes\n")
    hdr = f"{'p':>5} {'p%12':>5} {'p%8':>4} | {'(1,1)':>7} {'(1,3)':>7} {'(2,1)':>7} {'(2,3)':>7} | B1 B2  chi4(x0) rule  |g4-p*chi4(x0)|"
    print(hdr); print("-"*len(hdr))
    allJ_ok = allB = True
    for p in ps:
        res, b1, b2, c0, rule, err = run(p)
        cells = [fmt(res[k], p) for k in ((1,1),(1,3),(2,1),(2,3))]
        Jok = all(c in ("+p","-p") for c in cells) and len(set(cells)) == 1
        expected = "-p" if p % 3 == 1 else "+p"
        Jok = Jok and cells[0] == expected
        allJ_ok &= Jok; allB &= (b1 and b2 and c0 == rule)
        print(f"{p:>5} {p%12:>5} {p%8:>4} | " + " ".join(f"{c:>7}" for c in cells) +
              f" | {int(b1)}  {int(b2)}   {c0:>+3}   {rule:>+3}   {err:.2e}   {'OK' if Jok else 'MISMATCH'}")
    print()
    print(f"J == expected (all 4 character pairs, every prime): {allJ_ok}")
    print(f"B1+B2 + derived sign rule chi4(x0)=+1 iff p=7 mod 8: {allB}")
