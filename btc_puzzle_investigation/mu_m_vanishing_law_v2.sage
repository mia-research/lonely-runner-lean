# mu_m_vanishing_law_v1.sage
#
# PREREG: PREREG_mu_m_vanishing_law_v3.md  (RERUN: v2's run omitted C2, C4b and the
# cross-instrument comparison; an unrun control is not a passed control.)  (v1's design was TAUTOLOGICAL -- the Cartier
# stable rank is <= S by construction, so it cannot test P1.  P1 is tested ONLY against
# the point-count p-rank, which is an independent readout.)
#
# Exact integer / finite-field arithmetic throughout.  No float in the signal path.

import random, time
from collections import defaultdict

SEED = 20260806          # v3: fresh f draws; v2's sample is CONTAMINATED
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
print("="*104); print("mu_m VANISHING LAW -- RERUN.  PREREG_mu_m_vanishing_law_v3.md  seed %d" % SEED); print("="*104)
t0 = time.time()
C1P = {}
print("\n  (m,d)  genus   S   S_new   C1 primes")
for (m, d) in ROWS:
    g = genus(m, d)
    ps = [p for p in prime_range(d+1, PMAX+1) if p % m == m-1 and p**g <= C1_BUDGET]
    C1P[(m, d)] = ps
    print("  (%d,%d)   %-5d %-3d %-6d %s" % (m, d, g, S_of(m,d), S_new(m,d), ps if ps else "NONE - instrument-internal"))

# ---- K-plant
kp_ok = True
for (m, d) in ROWS[:4]:
    B = basis_gen(m, d); n = len(B); D = dimsV(m, d)
    pairs = [(b, m-b, min(D[b], D[m-b])) for b in range(1, m) if b <= m-b]
    targets = set([0])
    for (b, c, mn) in pairs:
        targets |= set(range(0, (mn if b==c else 2*mn)+1, 1 if b==c else 2))
    for r in sorted(targets):
        M = matrix(GF(101), n, n); placed = 0
        for (b, c, mn) in pairs:
            if placed >= r: break
            rb = [j for j,(a,bb) in enumerate(B) if bb == b]; rc = [j for j,(a,bb) in enumerate(B) if bb == c]
            if b == c:
                for k in range(min(mn, r - placed)): M[rb[k], rb[k]] = 1; placed += 1
            else:
                for k in range(mn):
                    if placed + 2 > r: break
                    M[rc[k], rb[k]] = 1; M[rb[k], rc[k]] = 1; placed += 2
        if stable_rank(M) != placed: kp_ok = False
print("\nK-plant : %s" % ("PASS" if kp_ok else "FAIL -> VOID"))

# ---- C4a
_ns = dict(globals())
exec(open("anew_m_support_v2.sage").read().split("# ============================================================ instrument checks")[0], _ns)
_cartier_m4 = _ns["cartier_matrix"]
assert PMAX == 200 and int(SEED) == 20260806, "namespace pollution: PMAX=%s SEED=%s" % (PMAX, SEED)
c4a_bad = c4a_n = 0
for p in (7, 11, 19, 23, 31, 43, 103):
    R = PolynomialRing(GF(p), 'x')
    for co in ([7,0,0,1],[5,2,0,1],[1,1,0,1],[3,-1,0,1]):
        fp = R([GF(p)(c) for c in co])
        if fp.discriminant() == 0: continue
        Mo, Bo = _cartier_m4(p, fp, 3); Mn, Bn = cartier_general(p, fp, 4, 3)
        c4a_n += 1
        if not (Bo == Bn and Mo == Mn): c4a_bad += 1
print("C4a     : %d comparisons, %d mismatches -> %s" % (c4a_n, c4a_bad, "PASS" if c4a_bad==0 else "FAIL -> VOID"))

# ---- C4b  (NEW: anchor; validates prank_pointcount against an independent quantity)
rngb = random.Random(int(SEED + 100)); c4b_bad = c4b_n = 0
for p in (7, 11, 19, 23, 31, 43, 47, 59):
    R = PolynomialRing(GF(p),'x')
    for _ in range(6):
        co = [rngb.randrange(p) for _ in range(3)] + [rngb.randrange(1,p)]
        f = R([GF(p)(c) for c in co])
        if f.discriminant() == 0: continue
        a3 = co[3]
        E = EllipticCurve(GF(p), [0, GF(p)(co[2]), 0, GF(p)(co[1])*GF(p)(a3), GF(p)(co[0])*GF(p)(a3)**2])
        expect = 1 if ((p + 1 - E.cardinality()) % p != 0) else 0
        pc, _ = prank_pointcount(p, co, 4, 3)
        M, B = cartier_general(p, f, 4, 3)
        c4b_n += 1
        if pc != expect or stable_rank(M) != expect: c4b_bad += 1
print("C4b     : %d rows, %d mismatches -> %s" % (c4b_n, c4b_bad, "PASS" if c4b_bad==0 else "FAIL -> VOID"))

# ---- C2  (NEW: wrong-pairing FIRING control)
rngc = random.Random(int(SEED + 200)); c2_cells = c2_fire = 0; c2_detail = []
for (m, d) in [(5,3), (7,3)]:
    D = dimsV(m,d); S = S_of(m,d); g = genus(m,d)
    for p in prime_range(d+1, 60):
        if p % m in (1, m-1) or p % m == 0: continue
        if p**g > 10**6: continue
        pinv = inverse_mod(p, m); seen=set(); Strue=0
        for b in range(1,m):
            if b in seen: continue
            orb=[]; x=b
            while x not in seen: seen.add(x); orb.append(x); x=(x*pinv)%m
            Strue += len(orb)*min(D[o] for o in orb)
        R = PolynomialRing(GF(p),'x'); mis = tot = 0
        for _ in range(4):
            co = [rngc.randrange(p) for _ in range(d)] + [rngc.randrange(1,p)]
            f = R([GF(p)(c) for c in co])
            if f.discriminant() == 0: continue
            pc, _ = prank_pointcount(p, co, m, d); tot += 1
            if pc != S: mis += 1
        if tot == 0: continue
        c2_cells += 1
        if Strue < S and mis == tot: c2_fire += 1
        c2_detail.append((m,d,p,p%m,S,Strue,mis,tot))
for row in c2_detail: print("   C2 cell (m,d)=(%d,%d) p=%-3d (p%%m=%d) S=%d S_true=%d mispredict %d/%d" % row)
c2_need = sum(1 for r in c2_detail if r[5] < r[4])
print("C2      : %d/%d cells with S_true<S mispredict on ALL rows -> %s"
      % (c2_fire, c2_need, "FIRES" if (c2_need>0 and c2_fire==c2_need) else "DOES NOT FIRE -> VOID"))

# ---- MAIN
print("\n### MAIN  p = -1 mod m\n")
rng = random.Random(int(SEED)); rows = []; c1_rows = []
for (m, d) in ROWS:
    g = genus(m, d); S = S_of(m, d)
    for p in [q for q in prime_range(d+1, PMAX+1) if q % m == m-1]:
        R = PolynomialRing(GF(p), 'x'); Fp = GF(p)
        drawn = tries = 0; fl = []
        while drawn < N_F and tries < 4000:
            tries += 1
            co = [rng.randrange(p) for _ in range(d)] + [rng.randrange(1, p)]
            if R([Fp(c) for c in co]).discriminant() != 0: fl.append(co); drawn += 1
        for i, co in enumerate(fl):
            fpol = R([Fp(c) for c in co])
            M, B = cartier_general(p, fpol, m, d)
            rec = dict(m=m, d=d, p=p, S=S, cartier=stable_rank(M), pairs=pair_ranks(M, B, m), co=co)
            if p in C1P[(m, d)] and i < N_C1:
                pc, _ = prank_pointcount(p, co, m, d); rec["pc"] = pc; c1_rows.append(rec)
            rows.append(rec)
        print("  (m,d)=(%d,%d) p=%-4d (%.0fs)" % (m, d, p, time.time()-t0))

print("\n" + "="*104); print("RESULTS"); print("="*104)
v1a = [r for r in c1_rows if r["pc"] > r["S"]]
v1b = [r for r in c1_rows if r["pc"] != r["cartier"]]
print("C1a point-count p-rank <= S      : %d rows ; VIOLATIONS %d %s" % (len(c1_rows), len(v1a), v1a[:3]))
print("C1b point-count == Cartier       : %d rows ; DISAGREEMENTS %d %s  <-- the check v2 never did"
      % (len(c1_rows), len(v1b), v1b[:3]))
print("Cartier stable rank > S          : %d  [forced; NOT evidence]" % len([r for r in rows if r["cartier"] > r["S"]]))
ka_fail = []
print("\n  (m,d)  S  S_new | cartier attains S | C1 rows, attain | K-attain")
for (m, d) in ROWS:
    sub = [r for r in rows if (r["m"],r["d"])==(m,d)]; subc = [r for r in c1_rows if (r["m"],r["d"])==(m,d)]
    att = sum(1 for r in sub if r["cartier"]==r["S"]); attc = sum(1 for r in subc if r["pc"]==r["S"])
    ok = att > 0
    if not ok: ka_fail.append((m,d))
    print("  (%d,%d)  %-2d %-5d | %4d/%-4d | %3d, %3d | %s%s" % (m,d,S_of(m,d),S_new(m,d),att,len(sub),
          len(subc),attc,"PASS" if ok else "FAIL", "" if subc else "  (no C1 - instrument-internal)"))
b23 = defaultdict(int)
for r in [r for r in rows if (r["m"],r["d"])==(5,3)]: b23[r["pairs"].get((2,3))] += 1
print("\n  P3 (5,3) {2,3} stable rank : %s   [pre-registered BINARY {0,2}]" % dict(b23))
allpass = (len(v1a)==0 and len(v1b)==0 and c4a_bad==0 and c4b_bad==0 and kp_ok
           and c2_need>0 and c2_fire==c2_need and not ka_fail)
print("\nALL CONTROLS PASS: %s   [if False the run is VOID]" % allpass)
print("elapsed %.0fs" % (time.time()-t0)); print("="*104)
