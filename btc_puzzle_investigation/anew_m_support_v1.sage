# anew_m_support_v1.sage
#
# PREREG: PREREG_anew_m_support_v1.md.  Question: the REALIZED support of m = b2/p over
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
    b1 = nE1 - nC1
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
       <=> the cover is isomorphic to some w^4 = x^3 + B.  Decidable from the label."""
    return label[0] == 0

# ============================================================ instrument checks

print("=" * 100)
print("m-SUPPORT RUN.  PREREG_anew_m_support_v1.md   seed %d" % SEED)
print("=" * 100)
t_start = time.time()

print("\n### V1  fast numpy counters vs the Sage reference implementation (instrument check)\n")
v1_bad = 0; v1_n = 0
for p in (7, 11, 19, 23, 31, 43, 67, 103):
    for nm, co in CURATED:
        R = PolynomialRing(GF(p), 'x')
        if R([GF(p)(c) for c in co]).discriminant() == 0: continue
        a1 = counts_fp(p, co);  b1_ = counts_sage(GF(p), co)
        a2 = counts_fp2(p, co); b2_ = counts_sage(GF(p**2, 'g'), co)
        v1_n += 2
        if a1 != b1_: v1_bad += 1; print("  MISMATCH F_p  p=%d %s  fast=%s sage=%s" % (p, nm, a1, b1_))
        if a2 != b2_: v1_bad += 1; print("  MISMATCH F_p2 p=%d %s  fast=%s sage=%s" % (p, nm, a2, b2_))
print("  V1: %d comparisons, %d mismatches -> %s" % (v1_n, v1_bad, "PASS" if v1_bad == 0 else "FAIL"))

print("\n### K1  synthetic-input control: can the extractor REPORT each m in {-2,-1,0,1,2}?\n")
k1_ok = True
for p in (1051, 1063):
    for m_target in (-2, -1, 0, 1, 2):
        nC1, nE1, nC2, nE2 = synth_counts(p, m_target, 1234, 987654)
        got, b1v, b2v = extract_m(p, nC1, nE1, nC2, nE2)
        ok = (got == m_target)
        k1_ok = k1_ok and ok
        print("  p=%-6d planted m=%-3d -> extractor reports %-6s b1=%-3s b2=%-10s  %s"
              % (p, m_target, got, b1v, b2v, "ok" if ok else "FAIL"))
print("  K1: %s   [VOID the run if FAIL -- a null on m=-1 would be unfalsifiable]"
      % ("PASS" if k1_ok else "FAIL"))

# ============================================================ main sweep

def run_arm(tag, primes_list, rng):
    rows = []
    for p in primes_list:
        Fp = GF(p); R = PolynomialRing(Fp, 'x')
        fs = list(CURATED)
        drawn = 0; tries = 0
        while drawn < N_RANDOM and tries < 4000:
            tries += 1
            co = [rng.randrange(p) for _ in range(3)] + [rng.randrange(1, p)]
            if R([Fp(c) for c in co]).discriminant() != 0:
                fs.append(("r%d" % drawn, co)); drawn += 1
        fp2_tables(p)
        for nm, co in fs:
            fpol = R([Fp(c) for c in co])
            if fpol.discriminant() == 0:
                rows.append(dict(p=p, name=nm, excluded=True)); continue
            nC1, nE1 = counts_fp(p, co)
            nC2, nE2 = counts_fp2(p, co)
            m, b1v, b2v = extract_m(p, nC1, nE1, nC2, nE2)
            M, B = cartier_matrix(p, fpol, 3)
            N = new_block(M, B)
            srank = (N**(3 * N.nrows())).rank()
            lab = cover_class(p, co)
            rows.append(dict(p=p, name=nm, excluded=False, m=m, b1=b1v, b2=b2v,
                             srank=int(srank), label=lab, cm=is_cm_type(lab)))
        print("  [%s] p=%-5d done (%.0fs elapsed)" % (tag, p, time.time() - t_start))
    return rows

print("\n### MAIN arm  p = 3 mod 4,  %d primes in (%d, %d)\n" % (len(MAIN), PMIN, PMAX))
main_rows = run_arm("MAIN", MAIN, random.Random(int(SEED)))

print("\n### CONTROL arm  p = 1 mod 4  (K2: m must be UNDEFINED on >= 2/3 of rows)\n")
ctrl_rows = run_arm("CTRL", CONTROL, random.Random(int(SEED + 1)))

# ============================================================ controls and report

live_main = [r for r in main_rows if not r["excluded"]]
live_ctrl = [r for r in ctrl_rows if not r["excluded"]]

# K2
k2_undef = sum(1 for r in live_ctrl if r["m"] is None)
k2_rate = k2_undef / len(live_ctrl) if live_ctrl else 0
# K3 cross-instrument
k3_bad = sum(1 for r in live_main + live_ctrl
             if ((r["b1"] % r["p"] == 0 and r["b2"] is not None and r["b2"] % r["p"] == 0)
                 != (r["srank"] == 0)))
# K4 label validity
lab_m = defaultdict(set)
for r in live_main + live_ctrl:
    lab_m[(r["p"], r["label"])].add(r["m"])
k4_bad = sum(1 for k, v in lab_m.items() if len(v) > 1)
# K5 CM detector
k5_curated = all(is_cm_type(cover_class(p, co)) for p in MAIN[:3] for nm, co in CURATED[:3])
k5_noncm = any(not r["cm"] for r in live_main)

print("\n" + "=" * 100)
print("CONTROLS")
print("=" * 100)
print("V1 fast-vs-sage counters   : %s (%d comparisons, %d mismatches)"
      % ("PASS" if v1_bad == 0 else "FAIL", v1_n, v1_bad))
print("K1 synthetic m in {-2..2}  : %s" % ("PASS" if k1_ok else "FAIL -> VOID"))
print("K2 m UNDEFINED on p=1 mod4 : %d/%d = %.3f   [need >= 0.667]" % (k2_undef, len(live_ctrl), k2_rate))
print("K3 cross-instrument disagr : %d   [need 0]" % k3_bad)
print("K4 labels with mixed m     : %d   [need 0]" % k4_bad)
print("K5 curated x^3+B are CM    : %s ; some non-CM present: %s" % (k5_curated, k5_noncm))

print("\n" + "=" * 100)
print("REALIZED SUPPORT OF m  (MAIN arm, p = 3 mod 4)")
print("=" * 100)
by_m = defaultdict(set); by_m_rows = defaultdict(int)
by_m_cm = defaultdict(set); by_m_noncm = defaultdict(set)
for r in live_main:
    key = r["m"] if r["m"] is not None else "UNDEFINED"
    by_m[key].add((r["p"], r["label"])); by_m_rows[key] += 1
    (by_m_cm if r["cm"] else by_m_noncm)[key].add((r["p"], r["label"]))
allcls = set((r["p"], r["label"]) for r in live_main)
print("rows=%d   distinct cover classes N=%d   distinct primes=%d"
      % (len(live_main), len(allcls), len(MAIN)))
print("\n  m           classes   rows    CM-type   non-CM")
for key in sorted(by_m, key=lambda z: (isinstance(z, str), z)):
    print("  %-10s  %-8d  %-6d  %-8d  %-8d"
          % (key, len(by_m[key]), by_m_rows[key], len(by_m_cm[key]), len(by_m_noncm[key])))

print("\n  LOCK VALUES (g=2 iff m=+-1):  m=+1 -> %d classes ;  m=-1 -> %d classes"
      % (len(by_m.get(1, ())), len(by_m.get(-1, ()))))

N = len(allcls); NP = len(MAIN)
print("\nPOWER (pre-committed).  If m=-1 occurs in a fraction q of classes, P(see none) = (1-q)^N.")
print("  class-based  N=%d  =>  95%% upper bound q <= %s" % (N, (1 - RR(0.05)**(RR(1)/N)) if N else "n/a"))
print("  prime-based  N=%d  =>  95%% upper bound q <= %s   [CONSERVATIVE: m is heavily"
      % (NP, (1 - RR(0.05)**(RR(1)/NP)) if NP else "n/a"))
print("     determined by p mod 12, so cover classes at one prime are NOT independent;")
print("     the prime-based bound is the one to quote.]")

exc = [(r["p"], r["name"]) for r in main_rows + ctrl_rows if r["excluded"]]
print("\nexclusions (disc f = 0 mod p), derived from the sample: %s" % sorted(exc))
print("\nelapsed %.0fs" % (time.time() - t_start))
print("=" * 100)
