# mu_m_vanishing_law_v1.sage
#
# PREREG: PREREG_mu_m_vanishing_law_v2.md  (v1's design was TAUTOLOGICAL -- the Cartier
# stable rank is <= S by construction, so it cannot test P1.  P1 is tested ONLY against
# the point-count p-rank, which is an independent readout.)
#
# Exact integer / finite-field arithmetic throughout.  No float in the signal path.

import random, time
from collections import defaultdict

SEED = 20260805
N_F = 40                 # seeded-random f per (m,d,p) for the descriptive Cartier readout
N_C1 = 8                 # of those, the first N_C1 also get the point-count p-rank (C1)
PMAX = 200
C1_BUDGET = 5 * 10**6    # p^g cap for the point-count leg

ROWS = [(4,3), (5,3), (3,4), (3,5), (4,5), (8,3), (7,3), (5,4)]

def dimsV(m, d): return {b: (b*d)//m for b in range(1, m)}
def genus(m, d):  return (m-1)*(d-1)//2
def S_of(m, d):
    D = dimsV(m, d); return sum(min(D[b], D[m-b]) for b in range(1, m))
def S_new(m, d):
    D = dimsV(m, d); return sum(min(D[b], D[m-b]) for b in range(1, m) if gcd(b, m) == 1)

# ---------------------------------------------------------------- Cartier, general m
def basis_gen(m, d):
    return [(a, b) for b in range(1, m) for a in range((b*d)//m)]

def cartier_general(p, fpol, m, d, corrupt=False):
    B = basis_gen(m, d); idx = {ab: j for j, ab in enumerate(B)}
    M = matrix(GF(p), len(B), len(B)); x = fpol.parent().gen()
    for j, (a, b) in enumerate(B):
        k = min(kk for kk in range(m) if (p*kk + b) % m == 0)
        t = (b + p*k)//m
        e = p - t
        if e < 0: raise RuntimeError("neg exponent m=%d b=%d p=%d" % (m, b, p))
        g = x**a * fpol**e
        bp = (b*p) % m if corrupt else m - k          # corrupt = the gate's F1 probe
        if bp == 0: bp = m
        dg = g.degree(); i = 0
        while i*p + p - 1 <= dg:
            c = g[i*p + p - 1]
            if c != 0 and (i, bp) in idx: M[idx[(i, bp)], j] = c
            i += 1
    return M, B

def stable_rank(M):
    N = M.nrows()
    return int((M**(2*N)).rank()) if N else 0

def pair_ranks(M, B, m):
    """stable rank restricted to each unordered pair {b, m-b}."""
    out = {}
    for b in range(1, m):
        c = m - b
        if b > c: continue
        idxs = [j for j, (a, bb) in enumerate(B) if bb in (b, c)]
        if not idxs: out[(b, c)] = 0; continue
        sub = M.matrix_from_rows_and_columns(idxs, idxs)
        out[(b, c)] = stable_rank(sub)
    return out

# ---------------------------------------------------------------- point-count p-rank (C1)
def count_C(F, fco, m):
    q = F.cardinality(); gm = gcd(m, q-1); e = (q-1)//gm
    n = 1                                     # one rational point at infinity (gcd(m,d)=1)
    for x in F:
        v = F(0)
        for c in reversed(fco): v = v*x + F(c)
        if v == 0: n += 1
        elif v**e == 1: n += gm
    return n

def prank_pointcount(p, fco, m, d):
    """p-rank from the Newton polygon of L_C.  Independent of the Cartier code."""
    g = genus(m, d)
    s = []                                    # power sums s_n = sum alpha_i^n
    for n in range(1, g+1):
        Nn = count_C(GF(p**n, 'g'), fco, m)
        s.append(p**n + 1 - Nn)
    # Newton's identities -> e_1..e_g  (char poly of Frobenius on H^1, degree 2g)
    e = [ZZ(1)]
    for n in range(1, g+1):
        acc = ZZ(0)
        for i in range(1, n+1):
            acc += (-1)**(i-1) * e[n-i] * s[i-1]
        e.append(acc / n)
    a = [ZZ(x) for x in e]                    # a[i] = e_i, i = 0..g
    coeffs = a[:]                             # extend by the functional equation
    for i in range(g+1, 2*g+1):
        coeffs.append(p**(i-g) * a[2*g-i])
    # p-rank = number of unit roots = max j with v_p(coeff_j) = 0
    pr = 0
    for j in range(0, 2*g+1):
        if coeffs[j] % p != 0: pr = j
    return min(pr, g), coeffs

# ---------------------------------------------------------------- report
print("="*104); print("mu_m VANISHING LAW.  PREREG_mu_m_vanishing_law_v2.md  seed %d" % SEED); print("="*104)
t0 = time.time()
print("\n### Predictions (from S; computed before any curve is examined)\n")
print("  (m,d)  genus   S   S_new   C1 primes (p = -1 mod m, p > d, p<=%d, p^g <= %.0e)" % (PMAX, C1_BUDGET))
C1P = {}
for (m, d) in ROWS:
    g = genus(m, d)
    ps = [p for p in prime_range(d+1, PMAX+1) if p % m == m-1 and p**g <= C1_BUDGET]
    C1P[(m, d)] = ps
    print("  (%d,%d)   %-5d %-3d %-6d %s" % (m, d, g, S_of(m,d), S_new(m,d), ps if ps else "NONE - instrument-internal"))

print("\n### K-plant  CONTROL: does the readout report a PLANTED stable rank?\n")
print("  NOTE (derived): on a pair {b, m-b} with b != m-b the stable rank is")
print("  rank((BA)^N) + rank((AB)^N), and those two are equal, so the pair's contribution")
print("  is ALWAYS EVEN.  Only achievable ranks are planted.")
kp_ok = True
for (m, d) in ROWS[:4]:
    B = basis_gen(m, d); n = len(B); D = dimsV(m, d)
    # achievable per-pair contributions
    pairs = []
    for b in range(1, m):
        c = m - b
        if b > c: continue
        pairs.append((b, c, min(D[b], D[c])))
    targets = set([0])
    for (b, c, mn) in pairs:
        step = 1 if b == c else 2
        cap = mn if b == c else 2*mn
        targets |= set(range(0, cap+1, step))
    for r in sorted(targets):
        M = matrix(GF(101), n, n); placed = 0
        for (b, c, mn) in pairs:
            if placed >= r: break
            rb = [j for j,(a,bb) in enumerate(B) if bb == b]
            rc = [j for j,(a,bb) in enumerate(B) if bb == c]
            if b == c:
                for k in range(min(mn, r - placed)):
                    M[rb[k], rb[k]] = 1; placed += 1
            else:
                for k in range(mn):
                    if placed + 2 > r: break
                    M[rc[k], rb[k]] = 1; M[rb[k], rc[k]] = 1; placed += 2
        got = stable_rank(M)
        if got != placed: kp_ok = False
        print("  (m,d)=(%d,%d) planted %d -> reported %d  %s" % (m, d, placed, got, "ok" if got == placed else "FAIL"))
print("  K-plant: %s" % ("PASS" if kp_ok else "FAIL -> VOID"))

print("\n### C4a  CONTROL: generalized-m code must reproduce the m=4 matrix ENTRYWISE\n")
# Load the m=4 reference into an ISOLATED namespace -- a bare exec() clobbers this
# script's own PMAX/SEED with that file's values (caught by the smoke test).
_ns = dict(globals())
exec(open("anew_m_support_v2.sage").read().split("# ============================================================ instrument checks")[0], _ns)
_cartier_m4 = _ns["cartier_matrix"]
assert PMAX == 200 and int(SEED) == 20260805, "namespace pollution: PMAX=%s SEED=%s" % (PMAX, SEED)
c4a_bad = 0; c4a_n = 0
for p in (7, 11, 19, 23, 31, 43, 103):
    R = PolynomialRing(GF(p), 'x')
    for co in ([7,0,0,1], [5,2,0,1], [1,1,0,1], [3,-1,0,1]):
        fp = R([GF(p)(c) for c in co])
        if fp.discriminant() == 0: continue
        M_old, B_old = _cartier_m4(p, fp, 3)
        M_new, B_new = cartier_general(p, fp, 4, 3)
        c4a_n += 1
        if not (B_old == B_new and M_old == M_new): c4a_bad += 1
print("  C4a: %d comparisons, %d mismatches -> %s" % (c4a_n, c4a_bad, "PASS" if c4a_bad == 0 else "FAIL -> VOID"))

print("\n### MAIN  p = -1 mod m\n")
rng = random.Random(int(SEED))
rows = []; c1_rows = []
for (m, d) in ROWS:
    g = genus(m, d); S = S_of(m, d)
    for p in [q for q in prime_range(d+1, PMAX+1) if q % m == m-1]:
        R = PolynomialRing(GF(p), 'x'); Fp = GF(p)
        drawn = 0; tries = 0; fl = []
        while drawn < N_F and tries < 4000:
            tries += 1
            co = [rng.randrange(p) for _ in range(d)] + [rng.randrange(1, p)]
            if R([Fp(c) for c in co]).discriminant() != 0: fl.append(co); drawn += 1
        for i, co in enumerate(fl):
            fpol = R([Fp(c) for c in co])
            M, B = cartier_general(p, fpol, m, d)
            sr = stable_rank(M); pr_pairs = pair_ranks(M, B, m)
            rec = dict(m=m, d=d, p=p, S=S, g=g, cartier=sr, pairs=pr_pairs, co=co)
            if p in C1P[(m, d)] and i < N_C1:
                pc, _ = prank_pointcount(p, co, m, d)
                rec["pc"] = pc; c1_rows.append(rec)
            rows.append(rec)
        print("  (m,d)=(%d,%d) p=%-4d  done (%.0fs)" % (m, d, p, time.time()-t0))

print("\n" + "="*104); print("RESULTS"); print("="*104)
viol = [r for r in c1_rows if r["pc"] > r["S"]]
print("C1  point-count p-rank vs S  : %d rows covered ; VIOLATIONS (pc > S): %d  %s"
      % (len(c1_rows), len(viol), viol[:3] if viol else ""))
print("    (a violation REFUTES the pairing mechanism; the Cartier readout CANNOT violate S)")
cart_viol = [r for r in rows if r["cartier"] > r["S"]]
print("Cartier stable rank > S      : %d  [must be 0 -- forced by construction, NOT evidence]" % len(cart_viol))
print("C4a entrywise m=4 regression : %s" % ("PASS" if c4a_bad == 0 else "FAIL"))
print("K-plant                      : %s" % ("PASS" if kp_ok else "FAIL"))

print("\n  per-(m,d): P2 rate = fraction attaining p-rank == S   [K-attain needs >=1 attaining row]")
for (m, d) in ROWS:
    sub  = [r for r in rows if (r["m"], r["d"]) == (m, d)]
    subc = [r for r in c1_rows if (r["m"], r["d"]) == (m, d)]
    att  = sum(1 for r in sub if r["cartier"] == r["S"])
    attc = sum(1 for r in subc if r["pc"] == r["S"])
    cov  = "COVERED" if subc else "instrument-internal (no C1)"
    print("  (%d,%d) S=%-2d S_new=%-2d | cartier attains S: %4d/%-4d | C1 rows %3d, attain %3d | %s"
          % (m, d, S_of(m,d), S_new(m,d), att, len(sub), len(subc), attc, cov))

print("\n  P3 at (5,3): the {2,3} summand stable rank -- pre-registered as BINARY {0,2}")
b23 = defaultdict(int)
for r in [r for r in rows if (r["m"], r["d"]) == (5, 3)]:
    b23[r["pairs"].get((2,3), None)] += 1
print("   distribution: %s   [values other than 0 or 2 would refute the pre-registered binarity]" % dict(b23))
print("\nelapsed %.0fs" % (time.time()-t0)); print("="*104)
