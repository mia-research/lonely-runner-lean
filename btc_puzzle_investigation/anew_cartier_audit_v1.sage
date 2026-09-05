# anew_cartier_audit_v1.sage
#
# PREREG: PREREG_anew_supersingularity_reaudit_v2.md, hypotheses H-B / H-C,
#         controls C1, C2, C3, C4, C5, PC.
#
# Object: C : w^4 = f(x), f separable of degree D over F_p, p > 3, gcd(4,D)=1.
#         H^0(C,Omega) is mu_4-graded: V_b = span{ x^a dx / w^b }, a < floor(D b/4).
#         V_2 = the E-part (E : y^2 = f) ; V_1 (+) V_3 = the A_new part.
#         Cartier operator, p^-1-semilinear:  C(sum c_i x^i dx) = sum c_{ip+p-1}^{1/p} x^i dx.
#
# Exponent table (prereg v2 sec.2):
#   k_b = least k>=0 with p*k = -b mod 4 ;  t_b = (b + p*k_b)/4 ;  f-exponent = p - t_b
#   image of V_b lands in V_{b'} with b' = 4 - k_b.
#
# Arms:  MAIN     D=3, p = 3 mod 4   (new-part block is FORCED to vanish under H-B)
#        CONTROL  D=3, p = 1 mod 4   (C2: instrument liveness)
#        PLANTED  D=5, p = 3 mod 4   (PC: dim V_1 = 1, so vanishing is NOT forced -- can fire)
#
# All arithmetic exact over finite fields / ZZ.  No float anywhere.

import random, time
from collections import defaultdict

SEED = 20260802
N_RANDOM = 6
C5_PRIME_CAP = 251          # prereg sec.4 compute bound, fixed before the run

CURATED = [(0,0,0,1, "x^3+7",     [7,0,0,1]),
           (0,0,0,1, "x^3+2",     [2,0,0,1]),
           (0,0,0,1, "x^3+11",    [11,0,0,1]),
           (0,0,0,1, "x^3+2x+5",  [5,2,0,1]),
           (0,0,0,1, "x^3+x+1",   [1,1,0,1]),
           (0,0,0,1, "x^3-x+3",   [3,-1,0,1])]
CURATED = [(nm, co) for (_,_,_,_, nm, co) in CURATED]

PREREG_EXCLUSIONS = {(7,"x^3+7"), (7,"x^3+2x+5"), (11,"x^3+11"),
                     (31,"x^3+x+1"), (101,"x^3+2x+5")}

MAIN    = [p for p in prime_range(7, 200) if p % 4 == 3] + [211, 251, 503, 1019]
CONTROL = [p for p in prime_range(5, 200) if p % 4 == 1] + [257, 509, 1013]
PLANTED = [p for p in MAIN if p <= 251]

# ---------------------------------------------------------------- basis / Cartier

def basis_list(D):
    return [(a, b) for b in (1, 2, 3) for a in range(D * b // 4)]

def cartier_matrix(p, fpol, D, perturb=None):
    """Matrix of the Cartier operator on H^0(Omega) in the graded basis.
       Returns (M, B, outside) ; outside = nonzero image coeffs landing off-basis."""
    B = basis_list(D)
    idx = {ab: j for j, ab in enumerate(B)}
    M = matrix(GF(p), len(B), len(B))
    x = fpol.parent().gen()
    outside = []
    for j, (a, b) in enumerate(B):
        k = min(kk for kk in range(4) if (p * kk + b) % 4 == 0)
        t = (b + p * k) // 4
        if perturb and b in perturb:
            t += perturb[b]
        e = p - t
        if e < 0:
            raise RuntimeError("negative exponent p-t at p=%d b=%d" % (p, b))
        g = x**a * fpol**e
        bp = 4 - k
        dg = g.degree()
        i = 0
        while i * p + p - 1 <= dg:
            c = g[i * p + p - 1]           # p-th root is the identity on F_p
            if c != 0:
                if (i, bp) in idx:
                    M[idx[(i, bp)], j] = c
                else:
                    outside.append(((a, b), (i, bp), c))
            i += 1
    return M, B, outside

def new_block(M, B):
    ni = [j for j, (a, b) in enumerate(B) if b in (1, 3)]
    return M.matrix_from_rows_and_columns(ni, ni)

# ---------------------------------------------------------------- point counts

_tab_cache = {}
def power_tables(F):
    key = F.cardinality()
    if key not in _tab_cache:
        s4, s2 = set(), set()
        for w in F:
            s4.add(w**4); s2.add(w**2)
        g4 = gcd(4, key - 1); g2 = 2
        _tab_cache[key] = (s4, s2, g4, g2)
    return _tab_cache[key]

def counts(F, fco):
    """(#C, #E) over F for C: w^4=f, E: y^2=f ; one point at infinity each (gcd(4,D)=1, D odd)."""
    s4, s2, g4, g2 = power_tables(F)
    nC = 1; nE = 1
    for x in F:
        v = F(0)
        for c in reversed(fco):
            v = v * x + F(c)
        if v == 0:
            nC += 1; nE += 1
        else:
            if v in s4: nC += g4
            if v in s2: nE += g2
    return nC, nE

# ---------------------------------------------------------------- iso classes (M-6)

def cover_class(p, fco):
    """Canonical label of the cover w^4 = f under x->alpha*x+beta and 4th-power scaling."""
    Fp = GF(p); R = PolynomialRing(Fp, 'x'); x = R.gen()
    f = R([Fp(c) for c in fco]); a3 = f[3]
    f = f / a3
    f = f(x - f[2] / 3)                       # depress
    P, Q = f[1], f[0]
    g = gcd(4, p - 1); z = Fp.multiplicative_generator()**((p - 1) // g)
    def coset(u):
        v = u**((p - 1) // g)
        for e in range(g):
            if z**e == v: return e
        raise RuntimeError
    best = None
    for al in Fp:
        if al == 0: continue
        cand = (ZZ(P / al**2), ZZ(Q / al**3), coset(a3 * al**3))
        if best is None or cand < best: best = cand
    return best

# ---------------------------------------------------------------- C3 divisors

def c3_divisors(p, fco, D):
    K = FunctionField(GF(p), 'x'); x = K.gen()
    R = PolynomialRing(K, 'T'); T = R.gen()
    fx = sum(K(int(c)) * x**i for i, c in enumerate(fco))
    L = K.extension(T**4 - fx, 'w'); w = L.gen()
    dxL = L(x).differential()
    want = [((0,1), False), ((0,2), True), ((1,2), False),
            ((0,3), True), ((1,3), True), ((2,3), False)]
    got = []
    for (a, b), _ in want:
        om = (L(x)**a / w**b) * dxL
        Dv = om.divisor()
        sup = Dv.support()
        mn = min([Dv.multiplicity(Pt) for Pt in sup]) if sup else 0
        got.append(((a, b), bool(mn >= 0)))
    return (got == want), L.genus(), got

# ---------------------------------------------------------------- driver

def run_arm(name, primes_list, D, rng, do_c3, do_c5, log):
    rows = []
    for p in primes_list:
        Fp = GF(p); R = PolynomialRing(Fp, 'x'); x = R.gen()
        cubics = []
        if D == 3:
            for nm, co in CURATED:
                cubics.append((nm, co, "observed" if (13 <= p <= 199) else "blind"))
        drawn = 0; tries = 0
        while drawn < N_RANDOM and tries < 500:
            tries += 1
            co = [rng.randrange(p) for _ in range(D)] + [rng.randrange(1, p)]
            fp = R([Fp(c) for c in co])
            if fp.discriminant() == 0: continue
            cubics.append(("rand%d_%s" % (drawn, "".join(str(c) for c in co)), co, "blind"))
            drawn += 1
        for nm, co, blindness in cubics:
            fp = R([Fp(c) for c in co])
            if fp.discriminant() == 0:
                log.append(("EXCLUDED", p, nm))
                continue
            M, B, outside = cartier_matrix(p, fp, D)
            N = new_block(M, B)
            nC, nE = counts(Fp, co)
            ap_C = p + 1 - nC
            c1 = (ZZ(M.trace()) - ap_C) % p == 0
            # stable rank of the semilinear operator on the new part
            srank = (N**(3 * N.nrows())).rank() if N.nrows() else 0
            anum = N.nrows() - N.rank()
            row = dict(p=p, name=nm, blind=blindness, D=D, C1=c1, outside=len(outside),
                       Nzero=(N == 0), Nrank=N.rank(), srank=srank, anum=anum,
                       trM=ZZ(M.trace()), apC=ap_C)
            if do_c5 and p <= C5_PRIME_CAP:
                F2 = GF(p**2, 'g')
                nC2, nE2 = counts(F2, co)
                b1 = nE - nC
                s2C = p**2 + 1 - nC2; s2E = p**2 + 1 - nE2
                b2 = (b1**2 - (s2C - s2E)) / 2
                assert b2 in ZZ
                b2 = ZZ(b2)
                ss_pc = (b1 % p == 0) and (b2 % p == 0)
                row.update(b1=b1, b2=b2, ss_pointcount=ss_pc,
                           C5=(ss_pc == (srank == 0)))
            if do_c3:
                ok3, gen, got = c3_divisors(p, co, D)
                row.update(C3=ok3, genus=gen)
            rows.append(row)
            log.append(("ROW", name, row))
            print("[%s] p=%-5d %-26s %-8s C1=%s C3=%s C5=%s | Nzero=%s rank=%d srank=%d a=%d%s"
                  % (name, p, nm, blindness,
                     "ok" if c1 else "FAIL",
                     ("ok" if row.get("C3") else "FAIL") if do_c3 else "-",
                     ("ok" if row.get("C5") else "FAIL") if "C5" in row else "-",
                     row["Nzero"], row["Nrank"], srank, anum,
                     ("  b1=%d b2=%d ssPC=%s" % (row["b1"], row["b2"], row["ss_pointcount"]))
                     if "b1" in row else ""))
    return rows

print("=" * 100)
print("A_new supersingularity re-audit -- Cartier arm.  PREREG v2.  seed %d" % SEED)
print("=" * 100)
t0 = time.time()
LOG = []

rng = random.Random(int(SEED))
print("\n### MAIN arm  (D=3, p = 3 mod 4)  -- new-part vanishing is FORCED under H-B\n")
main_rows = run_arm("MAIN", MAIN, 3, rng, do_c3=True, do_c5=True, log=LOG)

rng = random.Random(int(SEED + 1))
print("\n### CONTROL arm  (D=3, p = 1 mod 4)  -- C2 instrument liveness\n")
ctrl_rows = run_arm("CTRL", CONTROL, 3, rng, do_c3=True, do_c5=True, log=LOG)

rng = random.Random(int(SEED + 2))
print("\n### PLANTED control  (D=5, p = 3 mod 4)  -- dim V_1 = 1, vanishing NOT forced\n")
pl_rows = run_arm("PLNT", PLANTED, 5, rng, do_c3=False, do_c5=False, log=LOG)

# ------------------------------------------------------------------ C4
print("\n### C4  perturbation control (entrywise)\n")
c4 = []
for (arm, plist, D) in (("MAIN", MAIN[:6], 3), ("CTRL", CONTROL[:6], 3), ("PLNT", PLANTED[:6], 5)):
    for p in plist:
        Fp = GF(p); R = PolynomialRing(Fp, 'x')
        co = CURATED[1][1] if D == 3 else [1, 2, 0, 0, 1, 1]
        fp = R([Fp(c) for c in co])
        if fp.discriminant() == 0: continue
        M0, B, _ = cartier_matrix(p, fp, D)
        M2, _, _ = cartier_matrix(p, fp, D, perturb={2: 1})
        M3, _, _ = cartier_matrix(p, fp, D, perturb={3: 1})
        nC, _ = counts(Fp, co)
        apC = p + 1 - nC
        c1_pert = (ZZ(M2.trace()) - apC) % p == 0
        chg3 = (new_block(M3, B) != new_block(M0, B))
        c4.append((arm, p, not c1_pert, chg3))
        print("  [%s] p=%-5d  t2+1 breaks C1: %-5s |  t3+1 changes new-block: %s"
              % (arm, p, not c1_pert, chg3))

# ------------------------------------------------------------------ summary
def summarize(tag, rows):
    n = len(rows)
    c1 = sum(1 for r in rows if r["C1"])
    c3 = sum(1 for r in rows if r.get("C3"))
    c3n = sum(1 for r in rows if "C3" in r)
    c5 = sum(1 for r in rows if r.get("C5"))
    c5n = sum(1 for r in rows if "C5" in r)
    nz = sum(1 for r in rows if not r["Nzero"])
    off = sum(1 for r in rows if r["outside"])
    blind = [r for r in rows if r["blind"] == "blind"]
    nzb = sum(1 for r in blind if not r["Nzero"])
    print("\n%s : N=%d rows (blind %d / observed %d)" % (tag, n, len(blind), n - len(blind)))
    print("   C1 pass %d/%d | C3 pass %d/%d | C5 pass %d/%d | off-basis image %d"
          % (c1, n, c3, c3n, c5, c5n, off))
    print("   new-part block NON-ZERO : %d/%d  (blind subset: %d/%d)"
          % (nz, n, nzb, len(blind)))
    if rows and "anum" in rows[0]:
        from collections import Counter
        print("   a-number(new part) distribution : %s" % dict(Counter(r["anum"] for r in rows)))
        print("   stable-rank    distribution     : %s" % dict(Counter(r["srank"] for r in rows)))
    return dict(n=n, nz=nz, blind=len(blind), nzb=nzb, c1=c1, c3=c3, c3n=c3n, c5=c5, c5n=c5n, off=off)

print("\n" + "=" * 100)
print("SUMMARY")
print("=" * 100)
sm = summarize("MAIN    (D=3, p=3 mod 4)", main_rows)
sc = summarize("CONTROL (D=3, p=1 mod 4)", ctrl_rows)
sp = summarize("PLANTED (D=5, p=3 mod 4)", pl_rows)

# distinct cover-isomorphism classes on the main arm (M-6)
cls = defaultdict(set)
for r in main_rows:
    pass
print("\ndistinct cover classes, MAIN arm, curated x^3+B subfamily:")
for p in MAIN:
    Fp = GF(p)
    labs = set()
    for nm, co in CURATED[:3]:
        R = PolynomialRing(Fp, 'x')
        if R([Fp(c) for c in co]).discriminant() == 0: continue
        labs.add(cover_class(p, co))
    print("   p=%-5d  3 curated x^3+B  ->  %d distinct class(es)" % (p, len(labs)))

print("\n" + "=" * 100)
print("PRE-COMMITTED CONTROL VERDICTS")
print("=" * 100)
pc_rate = sp["nz"] / sp["n"] if sp["n"] else 0
c2_rate = sc["nzb"] / sc["blind"] if sc["blind"] else 0
print("PC  planted-control firing rate (D=5, p=3 mod 4) : %d/%d = %s   [need >= 1/3]"
      % (sp["nz"], sp["n"], pc_rate))
print("C2  control-arm firing rate, BLIND subset only   : %d/%d = %s   [need >= 1/3]"
      % (sc["nzb"], sc["blind"], c2_rate))
print("C1  pass                                          : MAIN %d/%d  CTRL %d/%d  PLNT %d/%d"
      % (sm["c1"], sm["n"], sc["c1"], sc["n"], sp["c1"], sp["n"]))
print("C3  pass                                          : MAIN %d/%d  CTRL %d/%d"
      % (sm["c3"], sm["c3n"], sc["c3"], sc["c3n"]))
print("C4  t2+1 breaks C1 everywhere                     : %s" % all(a for _, _, a, _ in c4))
print("C4  t3+1 changes new-block (CTRL/PLNT)            : %s"
      % all(d for arm, _, _, d in c4 if arm in ("CTRL", "PLNT")))
print("C4  t3+1 changes new-block (MAIN, expected False) : %s"
      % [d for arm, _, _, d in c4 if arm == "MAIN"])
print("C5  agreement                                     : MAIN %d/%d  CTRL %d/%d"
      % (sm["c5"], sm["c5n"], sc["c5"], sc["c5n"]))
print("MAIN-arm new-part non-zero (H-B falsifier)        : %d  [any > 0 => H-B RETRACTED]" % sm["nz"])
print("\nexclusions actually hit : %s" % sorted(set((p, nm) for tag, p, nm in LOG if tag == "EXCLUDED")))
print("pre-committed exclusions: %s" % sorted(PREREG_EXCLUSIONS))
print("\nelapsed %.1fs" % (time.time() - t0))
print("=" * 100)
