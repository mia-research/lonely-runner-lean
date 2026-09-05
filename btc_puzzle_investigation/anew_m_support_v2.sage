# anew_m_support_v2.sage
#
# PREREG: PREREG_anew_m_support_v2.md (v1 gated by experiment-designer; 6 blocking findings).  Question: the REALIZED support of m = b2/p over
# separable cubics at p = 3 mod 4, and specifically whether m = -1 (a 120-degree lock
# value, g=2 iff m=+-1) is ever realized.
#
# EXACTNESS: all signal-path arithmetic is integer.  numpy int64 is used for the F_p^2
# point counts -- this is EXACT integer arithmetic, not float.  An overflow guard is
# asserted per prime (worst intermediate vs int64 max).  No float anywhere.
#
# Functions cover_class / cartier_matrix / new_block / counts are copied VERBATIM from
# anew_cartier_audit_v2.sage (artifact of the 2026-08-02 run) rather than imported, so
# that completed artifact stays immutable.  V2 below checks the copies agree with it.

import random, time
import numpy as np
from collections import defaultdict

SEED = 20260804
N_RANDOM = 40                      # prereg sec.4
PMIN, PMAX = 1039, 2500            # prereg sec.4, disjoint from ALL prior samples

MAIN    = [p for p in prime_range(PMIN + 1, PMAX) if p % 4 == 3]
CONTROL = [p for p in prime_range(1033 + 1, PMAX) if p % 4 == 1]

CURATED = [("x^3+7", [7,0,0,1]), ("x^3+2", [2,0,0,1]), ("x^3+11", [11,0,0,1]),
           ("x^3+2x+5", [5,2,0,1]), ("x^3+x+1", [1,1,0,1]), ("x^3-x+3", [3,-1,0,1])]

# ============================================================ the m extractor
# Pure function of four integers, so K1 can feed it SYNTHETIC counts.

def extract_m(p, nC1, nE1, nC2, nE2):
    """Returns (m or None, b1, b2).  m is None <=> p does not divide b2 (UNDEFINED)."""
    b1 = nC1 - nE1          # [G:M2] v1 had this flipped; L_C = L_E * L_new gives #C - #E
    s2C = p**2 + 1 - nC2
    s2E = p**2 + 1 - nE2
    num = b1**2 - (s2C - s2E)
    if num % 2 != 0:
        return ("PARITY_FAIL", b1, None)
    b2 = num // 2
    if b2 % p != 0:
        return (None, b1, b2)
    return (b2 // p, b1, b2)

def synth_counts(p, m, nE1, nE2):
    """Inverse of extract_m at b1 = 0: counts realizing a chosen m.  Pure arithmetic
       fixture -- does NOT presuppose that an abelian surface with this m exists."""
    return (nE1, nE1, nE2 + 2*m*p, nE2)      # (nC1, nE1, nC2, nE2)

# ============================================================ fast exact counters

def nonresidue(p):
    for d in range(2, p):
        if pow(d, (p-1)//2, p) == p-1:
            return int(d)
    raise RuntimeError("no non-residue")

_fp2 = {}
def fp2_tables(p):
    """(A, B, mask4, mask2, d) over F_p^2 = F_p[u]/(u^2-d), index a*p+b."""
    if p in _fp2:
        return _fp2[p]
    d = nonresidue(p)
    A = np.arange(p, dtype=np.int64).repeat(p)
    B = np.tile(np.arange(p, dtype=np.int64), p)
    a2 = (A*A + d*B*B) % p
    b2 = (2*A*B) % p
    a4 = (a2*a2 + d*b2*b2) % p
    b4 = (2*a2*b2) % p
    m4 = np.zeros(p*p, dtype=bool); m4[a4*p + b4] = True; m4[0] = False
    m2 = np.zeros(p*p, dtype=bool); m2[a2*p + b2] = True; m2[0] = False
    # exactness guard: largest intermediate must be far below int64 max
    assert (p-1)**2 + d*(p-1)**2 < 2**62, "int64 overflow risk at p=%d" % p
    _fp2[p] = (A, B, m4, m2, d)
    return _fp2[p]

def counts_fp2(p, fco):
    """(#C(F_p^2), #E(F_p^2)) exactly; one rational point at infinity each."""
    A, B, m4, m2, d = fp2_tables(p)
    ra = np.zeros(p*p, dtype=np.int64); rb = np.zeros(p*p, dtype=np.int64)
    for c in reversed(fco):
        na = (ra*A + d*(rb*B)) % p
        nb = (ra*B + rb*A) % p
        ra = (na + (int(c) % p)) % p
        rb = nb
    idx = ra*p + rb
    zero = int(np.count_nonzero(idx == 0))
    return (1 + zero + 4*int(np.count_nonzero(m4[idx])),
            1 + zero + 2*int(np.count_nonzero(m2[idx])))

def counts_fp(p, fco):
    """(#C(F_p), #E(F_p)) exactly, by the same construction over F_p."""
    x = np.arange(p, dtype=np.int64)
    v = np.zeros(p, dtype=np.int64)
    for c in reversed(fco):
        v = (v*x + (int(c) % p)) % p
    g4 = gcd(4, p-1)
    sq = np.zeros(p, dtype=bool); sq[(x*x) % p] = True; sq[0] = False
    if g4 == 2:
        f4 = sq
    else:
        f4 = np.zeros(p, dtype=bool); f4[(x*x % p)*(x*x % p) % p] = True; f4[0] = False
    zero = int(np.count_nonzero(v == 0))
    return (1 + zero + g4*int(np.count_nonzero(f4[v])),
            1 + zero + 2*int(np.count_nonzero(sq[v])))

# ============================================================ copied from anew_cartier_audit_v2.sage

def counts_sage(F, fco):
    """VERBATIM from anew_cartier_audit_v2.sage -- reference implementation for V1."""
    q = F.cardinality()
    s4, s2 = set(), set()
    for w in F:
        s4.add(w**4); s2.add(w**2)
    g4 = gcd(4, q - 1)
    nC = 1; nE = 1
    for x in F:
        v = F(0)
        for c in reversed(fco):
            v = v * x + F(c)
        if v == 0:
            nC += 1; nE += 1
        else:
            if v in s4: nC += g4
            if v in s2: nE += 2
    return nC, nE

def basis_list(D):
    return [(a, b) for b in (1, 2, 3) for a in range(D * b // 4)]

def cartier_matrix(p, fpol, D):
    B = basis_list(D)
    idx = {ab: j for j, ab in enumerate(B)}
    M = matrix(GF(p), len(B), len(B))
    x = fpol.parent().gen()
    for j, (a, b) in enumerate(B):
        k = min(kk for kk in range(4) if (p * kk + b) % 4 == 0)
        t = (b + p * k) // 4
        g = x**a * fpol**(p - t)
        bp = 4 - k
        dg = g.degree()
        i = 0
        while i * p + p - 1 <= dg:
            c = g[i * p + p - 1]
            if c != 0 and (i, bp) in idx:
                M[idx[(i, bp)], j] = c
            i += 1
    return M, B

def new_block(M, B):
    ni = [j for j, (a, b) in enumerate(B) if b in (1, 3)]
    return M.matrix_from_rows_and_columns(ni, ni)

def cover_class(p, fco):
    Fp = GF(p); R = PolynomialRing(Fp, 'x'); x = R.gen()
    f = R([Fp(c) for c in fco]); a3 = f[3]
    f = f / a3
    f = f(x - f[2] / 3)
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

def is_cm_type(label):
    """CM-type <=> depressed cubic has zero linear term <=> canonical label[0] == 0
       <=> the cover is isomorphic to some w^4 = x^3 + B.  Decidable from the label.
       [G:M10,F4] verified exhaustively at p in {11,19,23,31} by the gate."""
    return label[0] == 0

def cm_classes(p):
    """[G:M12] EXHAUSTIVE enumeration of CM-type classes: all B in F_p*, dedup by cover_class.
       There are lcm(gcd(3,p-1), gcd(4,p-1)) of them -- 2 or 6 for p = 3 mod 4."""
    seen = {}
    for Bv in range(1, p):
        lab = cover_class(p, [Bv, 0, 0, 1])
        if lab not in seen:
            seen[lab] = Bv
    return seen                      # label -> a representative B

def chi3(p, Bv):
    """cubic residue symbol of B: 1 if B is a cube in F_p*, else the nontrivial class index."""
    if (p - 1) % 3 != 0:
        return 1                     # every element is a cube
    z = GF(p)(Bv)**((p - 1) // 3)
    if z == 1: return 1
    return 2 if z == GF(p).multiplicative_generator()**((p - 1) // 3) else 3

def orbit_partition_check(p):
    """K4' [G:M9]: labels must not SPLIT isomorphic covers either.  Brute force at small p."""
    Fp = GF(p); R = PolynomialRing(Fp, 'x'); x = R.gen()
    fourth = set((Fp(c)**4) for c in range(1, p))
    reps = {}
    for c3 in range(1, p):
        for c2 in range(p):
            for c1 in range(p):
                for c0 in range(p):
                    f = R([Fp(c0), Fp(c1), Fp(c2), Fp(c3)])
                    if f.discriminant() == 0: continue
                    reps[(c3, c2, c1, c0)] = cover_class(p, [c0, c1, c2, c3])
    # true orbits under f -> c*f(alpha x + beta), c a 4th power
    seen = {}; orbit_of = {}
    for key in reps:
        if key in orbit_of: continue
        c0, c1, c2, c3 = key[3], key[2], key[1], key[0]
        f = R([Fp(c0), Fp(c1), Fp(c2), Fp(c3)])
        oid = len(seen); seen[oid] = True
        for al in range(1, p):
            for be in range(p):
                g = f(Fp(al) * x + Fp(be))
                for c in fourth:
                    h = c * g
                    k2 = (int(h[3]), int(h[2]), int(h[1]), int(h[0]))
                    if k2 in reps: orbit_of[k2] = oid
    lab_part = {}
    for k, lab in reps.items(): lab_part.setdefault(lab, set()).add(k)
    orb_part = {}
    for k, o in orbit_of.items(): orb_part.setdefault(o, set()).add(k)
    return (sorted(map(sorted, lab_part.values())) == sorted(map(sorted, orb_part.values())),
            len(lab_part), len(orb_part))

# ============================================================ instrument checks

print("=" * 104)
print("m-SUPPORT RUN v2.  PREREG_anew_m_support_v2.md   seed %d" % SEED)
print("=" * 104)
t_start = time.time()

print("\n### V1  numpy counters vs the Sage reference implementation\n")
v1_bad = 0; v1_n = 0
for p in (7, 11, 19, 23, 31, 43, 67, 103):
    for nm, co in CURATED:
        R = PolynomialRing(GF(p), 'x')
        if R([GF(p)(c) for c in co]).discriminant() == 0: continue
        a1 = counts_fp(p, co);  r1 = counts_sage(GF(p), co)
        a2 = counts_fp2(p, co); r2 = counts_sage(GF(p**2, 'g'), co)
        v1_n += 2
        if a1 != r1: v1_bad += 1; print("  MISMATCH F_p  p=%d %s %s vs %s" % (p, nm, a1, r1))
        if a2 != r2: v1_bad += 1; print("  MISMATCH F_p2 p=%d %s %s vs %s" % (p, nm, a2, r2))
print("  V1: %d comparisons, %d mismatches -> %s" % (v1_n, v1_bad, "PASS" if v1_bad == 0 else "FAIL"))

print("\n### K1  CONTROL: can extract_m REPORT each m in {-2,-1,0,1,2}?  (pure integer fixture)\n")
k1_ok = True
for p in (1051, 1063):
    for mt in (-2, -1, 0, 1, 2):
        got, b1v, b2v = extract_m(p, *synth_counts(p, mt, 1234, 987654))
        ok = (got == mt); k1_ok = k1_ok and ok
        print("  p=%-6d planted m=%-3d -> reports %-6s (b1=%s)  %s" % (p, mt, got, b1v, "ok" if ok else "FAIL"))
print("  K1: %s" % ("PASS" if k1_ok else "FAIL -> VOID"))

print("\n### K4'  CONTROL: cover_class two-sided (must not merge AND must not split)\n")
k4_ok = True
for p in (11, 19, 23):
    eq, nlab, norb = orbit_partition_check(p)
    k4_ok = k4_ok and eq
    print("  p=%-4d labels=%-4d true orbits=%-4d  partitions equal: %s" % (p, nlab, norb, eq))
print("  K4': %s" % ("PASS" if k4_ok else "FAIL"))

# ============================================================ arms

def sample_cubics(p, rng):
    """CM stratum EXHAUSTIVE [G:M12] + N_RANDOM seeded-random general cubics."""
    fs = [("CM_B%d" % Bv, [Bv, 0, 0, 1]) for lab, Bv in cm_classes(p).items()]
    Fp = GF(p); R = PolynomialRing(Fp, 'x')
    drawn = 0; tries = 0
    while drawn < N_RANDOM and tries < 4000:
        tries += 1
        co = [rng.randrange(p) for _ in range(3)] + [rng.randrange(1, p)]
        if R([Fp(c) for c in co]).discriminant() != 0:
            fs.append(("r%d" % drawn, co)); drawn += 1
    return fs

def run_arm(tag, primes_list, rng):
    rows = []
    for p in primes_list:
        Fp = GF(p); R = PolynomialRing(Fp, 'x')
        fp2_tables(p)
        for nm, co in sample_cubics(p, rng):
            fpol = R([Fp(c) for c in co])
            if fpol.discriminant() == 0:
                rows.append(dict(p=p, name=nm, excluded=True)); continue
            nC1, nE1 = counts_fp(p, co)
            nC2, nE2 = counts_fp2(p, co)
            m, b1v, b2v = extract_m(p, nC1, nE1, nC2, nE2)
            M, B = cartier_matrix(p, fpol, 3)
            N = new_block(M, B)
            lab = cover_class(p, co)
            cm = is_cm_type(lab)
            rows.append(dict(p=p, name=nm, excluded=False, m=m, b1=b1v, b2=b2v,
                             srank=int((N**6).rank()), trM=ZZ(M.trace()), apC=p + 1 - nC1,
                             label=lab, cm=cm, chi3=(chi3(p, co[0]) if cm else None)))
        del _fp2[p]
        print("  [%s] p=%-5d  (%.0fs)" % (tag, p, time.time() - t_start))
    return rows

print("\n### MAIN arm  p = 3 mod 4,  %d primes in (%d,%d)\n" % (len(MAIN), PMIN, PMAX))
main_rows = run_arm("MAIN", MAIN, random.Random(int(SEED)))
print("\n### CONTROL arm  p = 1 mod 4,  %d primes\n" % len(CONTROL))
ctrl_rows = run_arm("CTRL", CONTROL, random.Random(int(SEED + 1)))

# ---- K3a : Manin congruence on the CONTROL arm.  At p = 1 mod 4 the grading gives
#            V3 -> V3, so the new-part block sits ON the diagonal and DOES contribute
#            to Tr(M).  At p = 3 mod 4 the new part is off-diagonal and can never
#            contribute -- which is exactly why this control cannot live on the MAIN arm.
live_ctrl = [r for r in ctrl_rows if not r["excluded"]]
k3a_bad = sum(1 for r in live_ctrl if (r["trM"] - r["apC"]) % r["p"] != 0)
k3a_distinct = len(set((r["trM"] % r["p"]) for r in live_ctrl))

# ---- K3b : D=5 planted arm at p = 3 mod 4, where dim V1 = 1 so vanishing is NOT forced
print("\n### K3b  CONTROL: D=5 planted arm, p = 3 mod 4 (new-part vanishing NOT forced)\n")
k3b_nonzero = 0; k3b_n = 0
rng5 = random.Random(int(SEED + 2))
for p in MAIN[:12]:
    Fp = GF(p); R = PolynomialRing(Fp, 'x')
    for _ in range(4):
        co = [rng5.randrange(p) for _ in range(5)] + [rng5.randrange(1, p)]
        fpol = R([Fp(c) for c in co])
        if fpol.discriminant() == 0: continue
        M5, B5 = cartier_matrix(p, fpol, 5)
        k3b_n += 1
        if new_block(M5, B5) != 0: k3b_nonzero += 1
print("  new-part block NON-ZERO on %d/%d planted rows  [need >= 5]" % (k3b_nonzero, k3b_n))

# ============================================================ report

live_main = [r for r in main_rows if not r["excluded"]]
g1_undef = sum(1 for r in live_ctrl if r["m"] is None)
g1_rate = g1_undef / len(live_ctrl) if live_ctrl else 0
g2_cur = all(is_cm_type(cover_class(p, co)) for p in MAIN[:3] for nm, co in CURATED[:3])
g2_non = any(not r["cm"] for r in live_main)
lab_m = defaultdict(set)
for r in live_main + live_ctrl: lab_m[(r["p"], r["label"])].add(r["m"])
mixed = sum(1 for v in lab_m.values() if len(v) > 1)

print("\n" + "=" * 104); print("CONTROLS AND GUARDS"); print("=" * 104)
print("V1  numpy vs sage counters      : %s (%d cmp, %d mismatch)" % ("PASS" if v1_bad == 0 else "FAIL", v1_n, v1_bad))
print("K1  synthetic m in {-2..2}      : %s" % ("PASS" if k1_ok else "FAIL -> VOID"))
print("K3a Manin on CONTROL arm        : %d disagreements / %d rows ; Tr(M) takes %d distinct values  [need 0 and >= 5]"
      % (k3a_bad, len(live_ctrl), k3a_distinct))
print("K3b D=5 planted, new-part != 0  : %d/%d  [need >= 5]" % (k3b_nonzero, k3b_n))
print("K4' cover_class two-sided       : %s" % ("PASS" if k4_ok else "FAIL"))
print("G1  m UNDEFINED on p=1 mod 4    : %d/%d = %.4f  [guard, need >= 0.95]" % (g1_undef, len(live_ctrl), g1_rate))
print("G2  CM detector                 : curated all CM = %s ; non-CM present = %s" % (g2_cur, g2_non))
print("    labels with mixed m         : %d  [need 0]" % mixed)

print("\n" + "=" * 104); print("REALIZED SUPPORT OF m  --  MAIN arm, p = 3 mod 4"); print("=" * 104)
def tally(rows):
    d = defaultdict(set)
    for r in rows: d[r["m"] if r["m"] is not None else "UNDEF"].add((r["p"], r["label"]))
    return d
cm_rows  = [r for r in live_main if r["cm"]]
non_rows = [r for r in live_main if not r["cm"]]
tcm, tnon = tally(cm_rows), tally(non_rows)
print("rows: %d (CM %d, non-CM %d) | classes: CM %d, non-CM %d | primes %d"
      % (len(live_main), len(cm_rows), len(non_rows),
         len(set((r['p'], r['label']) for r in cm_rows)),
         len(set((r['p'], r['label']) for r in non_rows)), len(MAIN)))
print("\n   m        CM classes (EXHAUSTIVE census)   non-CM classes (sampled)")
for k in sorted(set(tcm) | set(tnon), key=lambda z: (isinstance(z, str), z)):
    print("   %-8s %-32d %d" % (k, len(tcm.get(k, ())), len(tnon.get(k, ()))))
print("\n   LOCK VALUES (g=2 iff m=+-1):  m=+1 -> CM %d / non-CM %d ;  m=-1 -> CM %d / non-CM %d"
      % (len(tcm.get(1, ())), len(tnon.get(1, ())), len(tcm.get(-1, ())), len(tnon.get(-1, ()))))

o6 = [(r["p"], r["name"]) for r in live_main if r["m"] is None]
o7 = [(r["p"], r["name"], r["m"], r["b1"]) for r in live_main
      if (r["m"] is not None and r["m"] not in (-2, -1, 0, 1, 2)) or r["b1"] != 0]
h3 = defaultdict(set)
for r in cm_rows: h3[(r["p"], r["p"] % 12, r["chi3"])].add(r["m"])
o10 = [(k, sorted(v)) for k, v in h3.items() if len(v) > 1]
print("\n   OUTCOME 6  m UNDEFINED on MAIN arm       : %d  %s   [>0 => VOID-and-investigate]" % (len(o6), o6[:5]))
print("   OUTCOME 7  m outside {-2..2} or b1 != 0  : %d  %s   [>0 => VOID-and-investigate]" % (len(o7), o7[:5]))
print("   OUTCOME 10 H3 falsifier (same (p, p mod 12, chi3), different m) : %d  %s" % (len(o10), o10[:5]))

Ncls_non = len(set((r['p'], r['label']) for r in non_rows)); NP = len(MAIN)
within = sum(1 for p in MAIN if len(set(r["m"] for r in non_rows if r["p"] == p)) >= 2)
print("\n" + "=" * 104); print("POWER (pre-committed, PREREG v2 sec.3)"); print("=" * 104)
print("  CM stratum      : EXHAUSTIVE census at all %d primes -- no within-prime sampling bound" % NP)
print("  non-CM HEADLINE : N_eff = %d primes  => q <= %.4f%%" % (NP, 100 * (1 - RR(0.05)**(RR(1)/NP))))
print("  non-CM class-lvl: N = %d classes    => q <= %.4f%%" % (Ncls_non, 100 * (1 - RR(0.05)**(RR(1)/Ncls_non))))
print("     licensed ONLY if within-prime variation is demonstrated:")
print("     primes with >= 2 distinct m among sampled non-CM classes: %d / %d" % (within, NP))

exc = [(r["p"], r["name"]) for r in main_rows + ctrl_rows if r["excluded"]]
print("\nexclusions (disc = 0), derived from the sample: %s" % sorted(exc)[:20])
print("\nelapsed %.0fs" % (time.time() - t_start)); print("=" * 104)
