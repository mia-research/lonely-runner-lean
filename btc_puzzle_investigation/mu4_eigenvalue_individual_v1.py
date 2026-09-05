#!/usr/bin/env sage
# RUN: sage mu4_eigenvalue_individual_v1.py
#
# Executes PREREG_mu4_eigenvalue_individual_v1.md EXACTLY.  Read that file first; every pass/fail
# condition below is copied from it, not invented here.
#
# OBJECT: the four INDIVIDUAL Frobenius eigenvalues of Frob_p on H^1(A_new), A_new = new part of
# Jac(C), C: w^4 = f(x).  At p = 3 mod 4 the mu4 argument forces b1 = 0, so
#      char(t) = t^4 + m p t^2 + p^2,   t = sqrt(p) z  =>  z^4 + m z^2 + 1 = 0,
# and the integer m = b2/p is the QUANTUM NUMBER naming each individual eigenvalue angle.
#
# H1: p = 11 mod 12                  => m = 2
# H2: p =  7 mod 12, f = x^3+B       => m = -2 if B is a cubic residue mod p, else m = 1
# H2b: within p = 7 mod 12, m depends on B only through the cubic character (underpowered, K=7).
#
# Window is OUT-OF-SAMPLE: 200 < p < 500, disjoint from the 13..199 training log.
#
# EXACTNESS: all of aC, aE, P1, P2, b1, b2, m, N_plus, N_minus, m_chi4 are Sage Integers.  Divisions
# are divisibility-checked then //.  Angles are fractions.Fraction by TABLE LOOKUP on m -- the v1
# script's QQbar/1e-9 root-finding path is BANNED from the verdict path (prereg section 8).

from sage.all import *
from fractions import Fraction
import sys, time

sys.stdout.reconfigure(line_buffering=True)

# ---------------------------------------------------------------- prereg section 2: angle table
ANGLE = {
    -2: (Fraction(0), Fraction(0), Fraction(1), Fraction(1)),
    -1: (Fraction(1, 6), Fraction(-1, 6), Fraction(5, 6), Fraction(-5, 6)),
     0: (Fraction(1, 4), Fraction(-1, 4), Fraction(3, 4), Fraction(-3, 4)),
     1: (Fraction(2, 3), Fraction(-2, 3), Fraction(1, 3), Fraction(-1, 3)),
     2: (Fraction(1, 2), Fraction(-1, 2), Fraction(1, 2), Fraction(-1, 2)),
}
ORDER = {-2: "1,1,2,2", -1: "12 (prim)", 0: "8 (prim)", 1: "3,3,6,6", 2: "4,4,4,4"}

def angles_str(m):
    if m not in ANGLE:
        return "-"
    return " ".join(("%s" % a) for a in ANGLE[m])


# ================================================================ ROUTE A  (statistic, section 2)
# Exact integer point counts of C over F_p and F_{p^2} + trace of E  ->  b1, b2, m.
# Speed: the quartic-class of every u in F_q is read off a generator-walk table (q multiplications),
# not q exponentiations.  Exact throughout (no float, no dlog of a key).

_QTAB = {}

def quartic_class_table(Fq, q):
    """dict: u -> (discrete log of u) mod 4, for all u in Fq^*.  Built by walking a generator.
       Cached on q: the table depends only on the field, never on the cubic."""
    if q in _QTAB:
        return _QTAB[q]
    g = Fq.multiplicative_generator()
    tab = {}
    cur = Fq(1)
    for k in range(q - 1):
        tab[cur] = k % 4
        cur = cur * g
    _QTAB[q] = tab
    return tab


def route_A(p, cubic, A, B):
    """returns (b1, b2, m_or_None) with m = b2/p when p | b2."""
    a2, a1, a0 = cubic
    aC = []
    for k in (1, 2):
        q = p ** k
        Fq = GF(q, 'a')
        d = gcd(4, q - 1)                 # #{w : w^4 = u} for u in the image
        tab = quartic_class_table(Fq, q)
        cnt = 0
        for x in Fq:
            u = x ** 3 + a2 * x ** 2 + a1 * x + a0
            if u == 0:
                cnt += 1
            else:
                # w^4 = u solvable iff u in image of 4th-power map = subgroup of index d
                #   <=> dlog(u) = 0 mod d ; and then there are exactly d solutions.
                if tab[u] % d == 0:
                    cnt += d
        aC.append(Integer(q + 1 - (cnt + 1)))     # one point at infinity (gcd(4,3)=1)
    t = Integer(EllipticCurve(GF(p), [A, B]).trace_of_frobenius())
    aE1 = t
    aE2 = t * t - 2 * p
    P1 = aC[0] - aE1
    P2 = aC[1] - aE2
    e1 = P1
    e2 = (P1 * P1 - P2) // 2
    assert (P1 * P1 - P2) % 2 == 0, "non-integral e2 at p=%d" % p
    b1 = -e1
    b2 = e2
    m = (b2 // p) if (b2 % p == 0) else None
    return Integer(b1), Integer(b2), (Integer(m) if m is not None else None)


# ================================================================ ROUTE B  (the FIRING control, section 5)
# INDEPENDENT enumeration of F_{p^2}, literal prereg formula.  Inputs: f and p ONLY.
# Forbidden from reading b2, P2, aC, aE, L_new or anything from route_A.

def route_B_chi4(p, cubic):
    """m_chi4 = (N_plus - N_minus)/p ,  N_pm = #{x in F_{p^2} : f(x)^((p^2-1)/4) = pm 1}."""
    a2, a1, a0 = cubic
    q = p ** 2
    Fq = GF(q, 'b')
    e = (q - 1) // 4
    one = Fq(1)
    mone = Fq(-1)
    Np = 0
    Nm = 0
    for x in Fq:
        u = x ** 3 + a2 * x ** 2 + a1 * x + a0
        if u == 0:
            continue
        z = u ** e
        if z == one:
            Np += 1
        elif z == mone:
            Nm += 1
    diff = Integer(Np - Nm)
    if diff % p != 0:
        return None, Integer(Np), Integer(Nm)
    return Integer(diff // p), Integer(Np), Integer(Nm)


# ================================================================ hypotheses (section 3)

def cubic_class(B, p):
    """B^((p-1)/3) mod p as an element of F_p (only meaningful when p = 1 mod 3)."""
    return Integer(pow(Integer(B), (p - 1) // 3, p))


def quad_class(B, p):
    return Integer(pow(Integer(B), (p - 1) // 2, p))


def predict_H1(p):
    return Integer(2)


def predict_H2(B, p):
    return Integer(-2) if cubic_class(B, p) == 1 else Integer(1)


# ================================================================ main

CM_CUBICS = [("CM  x^3+7", (0, 0, 7), 0, 7),
             ("CM  x^3+2", (0, 0, 2), 0, 2),
             ("CM  x^3+11", (0, 0, 11), 0, 11)]
NCM_CUBICS = [("nCM x^3+2x+5", (0, 2, 5), 2, 5),
              ("nCM x^3+x+1", (0, 1, 1), 1, 1),
              ("nCM x^3-x+3", (0, -1, 3), -1, 3)]
CUBICS = CM_CUBICS + NCM_CUBICS

WIN_LO, WIN_HI = 200, 500          # prereg section 6; only permitted truncation is HI -> 400
INSAMPLE_RECHECK = 30              # prereg section 5: 30 in-sample rows re-run as a readout check
PLANT2_ROWS = [(7, 211), (2, 227), (11, 239)]
PLANT3_PRIMES = [229, 233, 241, 257]


def main():
    t0 = time.time()
    primes = [Integer(p) for p in prime_range(WIN_LO + 1, WIN_HI) if p % 4 == 3]
    print("=" * 118)
    print("INDIVIDUAL FROBENIUS EIGENVALUES OF A_new  --  executing PREREG_mu4_eigenvalue_individual_v1.md")
    print("SCOPE: 6 cubics; p = 3 mod 4, %d < p < %d (%d primes); m = b2/p from exact point counts."
          % (WIN_LO, WIN_HI, len(primes)))
    print("WINDOW IS OUT-OF-SAMPLE (training log was 13 <= p <= 199).  TRUNCATION: none.")
    print("=" * 118)
    print("  primes: %s" % ", ".join(str(p) for p in primes))
    print()

    rows = []            # (label, isCM, B, p, b1, b2, m, m_chi4, agree)
    ctrl_fail = []

    hdr = ("cubic", "p", "p%12", "b1", "b2", "m_A", "m_chi4", "ctrl", "eigen-angles (units of pi)", "ord")
    print("  %-14s %-5s %-5s %5s %12s %5s %7s %6s  %-30s %s" % hdr)
    print("  " + "-" * 114)
    for lab, cub, A, B in CUBICS:
        for p in primes:
            if (4 * A ** 3 + 27 * B ** 2) % p == 0:
                print("  SKIP %s p=%d : singular reduction" % (lab, p))
                continue
            b1, b2, m = route_A(p, cub, A, B)
            mB, Np, Nm = route_B_chi4(p, cub)
            ok = (m is not None) and (mB is not None) and (m == mB)
            if not ok:
                ctrl_fail.append((lab, p, b1, b2, m, mB, Np, Nm))
            print("  %-14s %-5d %-5d %5d %12d %5s %7s %6s  %-30s %s"
                  % (lab, p, p % 12, b1, b2, str(m) if m is not None else "-",
                     str(mB) if mB is not None else "-", "ok" if ok else "FAIL",
                     angles_str(m) if m is not None else "-",
                     ORDER.get(m, "-") if m is not None else "-"))
            rows.append((lab, lab.startswith("CM"), B, p, b1, b2, m, mB, ok))
    print("  " + "-" * 114)
    print("  [route A/B wall time so far: %.1f s]" % (time.time() - t0))
    print()

    # ------------------------------------------------------- section 5: in-sample readout re-check
    print("=" * 118)
    print("CONTROL 1 (section 5) -- chi4 identity m = Re(S)/p, independent enumeration.")
    print("=" * 118)
    ins_primes = [Integer(p) for p in prime_range(13, 200) if p % 4 == 3]
    ins_rows = 0
    ins_bad = []
    for lab, cub, A, B in CUBICS:
        for p in ins_primes:
            if ins_rows >= INSAMPLE_RECHECK:
                break
            if (4 * A ** 3 + 27 * B ** 2) % p == 0:
                continue
            b1, b2, m = route_A(p, cub, A, B)
            mB, _, _ = route_B_chi4(p, cub)
            ins_rows += 1
            if m != mB:
                ins_bad.append((lab, p, m, mB))
        if ins_rows >= INSAMPLE_RECHECK:
            break
    print("  in-sample readout re-check (NOT evidence for H1/H2): %d rows, disagreements: %s"
          % (ins_rows, ins_bad if ins_bad else "NONE"))
    print("  out-of-sample control: %d rows, disagreements: %s"
          % (len(rows), ctrl_fail if ctrl_fail else "NONE"))
    control_ok = (not ctrl_fail) and (not ins_bad)
    print("  CONTROL 1 VERDICT: %s" % ("PASS" if control_ok else "FAIL -- readout broken"))
    print()

    # ------------------------------------------------------- section 5b: the three plants
    print("=" * 118)
    print("PLANTED CONTROLS (section 5b) -- all three must fire BEFORE any verdict.")
    print("=" * 118)

    # plant 1: deliberately false H1' : p = 11 mod 12 => m = 1
    p1_viol = [(lab, p, m) for (lab, isCM, B, p, b1, b2, m, mB, ok) in rows
               if isCM and p % 12 == 11 and m != 1]
    plant1 = len(p1_viol) > 0
    print("  PLANT 1 (mutated hypothesis H1' : p=11 mod 12 => m=1, deliberately FALSE)")
    print("     violations found: %d  -> %s" % (len(p1_viol), "FIRED (comparator works)" if plant1
                                                else "DID NOT FIRE -- comparator broken, HALT"))

    # plant 2: chi4 route on f+1 vs b2 route on f, three named rows
    print("  PLANT 2 (perturbed object: chi4 on f+1 vs b2 on f, rows %s)" % PLANT2_ROWS)
    p2_dis = 0
    for (B, p) in PLANT2_ROWS:
        p = Integer(p)
        cub = (0, 0, B)
        cub_pert = (0, 0, B + 1)
        _, _, m_f = route_A(p, cub, 0, B)
        m_pert, _, _ = route_B_chi4(p, cub_pert)
        d = (m_f != m_pert)
        p2_dis += 1 if d else 0
        print("     B=%-3d p=%-4d  m(b2 route, f)=%s   m(chi4 route, f+1)=%s  -> %s"
              % (B, p, m_f, m_pert, "DISAGREE" if d else "agree"))
    plant2 = p2_dis >= 1
    print("     disagreements: %d/3 -> %s" % (p2_dis, "FIRED" if plant2
                                              else "DID NOT FIRE -- control cannot fire, HALT"))

    # plant 3: p = 1 mod 4 must show b1 != 0
    print("  PLANT 3 (even-char-poly: p = 1 mod 4, B=7, must show b1 != 0 somewhere)")
    p3_nz = 0
    for p in PLANT3_PRIMES:
        p = Integer(p)
        b1, b2, m = route_A(p, (0, 0, 7), 0, 7)
        if b1 != 0:
            p3_nz += 1
        print("     p=%-4d (p%%4=%d)  b1=%-6d b2=%-10d %s" % (p, p % 4, b1, b2,
                                                             "b1 != 0" if b1 != 0 else "b1 == 0"))
    plant3 = p3_nz >= 1
    print("     rows with b1 != 0: %d/4 -> %s" % (p3_nz, "FIRED (b1=0 is measured)" if plant3
                                                  else "DID NOT FIRE -- b1 column suspect, HALT"))
    plants_ok = plant1 and plant2 and plant3
    print("  PLANTS VERDICT: %s" % ("ALL FIRED" if plants_ok else "FAILURE -- see above"))
    print()

    # ------------------------------------------------------- section 6/10 row 6: forced-column audit
    print("=" * 118)
    print("FORCED COLUMNS (section 4) -- reported, NOT counted as evidence.")
    print("=" * 118)
    b1_viol = [(lab, p, b1) for (lab, isCM, B, p, b1, b2, m, mB, ok) in rows if b1 != 0]
    div_viol = [(lab, p, b2) for (lab, isCM, B, p, b1, b2, m, mB, ok) in rows if m is None]
    print("  p=3 mod 4 rows with b1 != 0 : %s" % (b1_viol if b1_viol else "NONE (forced, as expected)"))
    print("  p=3 mod 4 rows with p nmid b2: %s" % (div_viol if div_viol else "NONE (forced, as expected)"))
    print("  |m| <= 2 on every row       : %s" % all(abs(r[6]) <= 2 for r in rows if r[6] is not None))
    print()

    if not (control_ok and plants_ok):
        print("=" * 118)
        print("PRE-COMMITMENT TABLE ROW 0 APPLIES: control failed or a plant did not fire.")
        print("NO verdict on H1, H2, H2b or the exploratory arm is reported.  Output ends here.")
        print("=" * 118)
        return

    # ------------------------------------------------------- verdicts, section 3/4/7
    cm = [r for r in rows if r[1]]
    print("=" * 118)
    print("VERDICT BLOCK (CM arm only; non-CM is EXPLORATORY and appears below with no prediction)")
    print("=" * 118)

    # ---- H1
    h1 = [r for r in cm if r[3] % 12 == 11]
    h1_viol = [(r[0], r[3], r[6]) for r in h1 if r[6] != predict_H1(r[3])]
    K1 = len(set((r[3], quad_class(r[2], r[3])) for r in h1))
    print("  H1 : p = 11 mod 12 => m = 2")
    print("     rows_checked = %d   distinct_configs K1 = %d   violations = %s"
          % (len(h1), K1, h1_viol if h1_viol else "NONE"))
    print("     null prob over distinct configs (H0: m ~ U{-2,1,2}) = 3^-%d = %.2e"
          % (K1, float(3.0 ** (-K1))))
    print("     adequacy bar K >= 10 : %s" % ("MET" if K1 >= 10 else "NOT MET"))

    # ---- H2
    h2 = [r for r in cm if r[3] % 12 == 7]
    h2_viol = [(r[0], r[3], r[6], predict_H2(r[2], r[3])) for r in h2 if r[6] != predict_H2(r[2], r[3])]
    K2 = len(set((r[3], cubic_class(r[2], r[3])) for r in h2))
    print("  H2 : p = 7 mod 12 => m = -2 if B is a cubic residue mod p, else m = 1")
    print("     rows_checked = %d   distinct_configs K2 = %d   violations = %s"
          % (len(h2), K2, h2_viol if h2_viol else "NONE"))
    print("     null prob over distinct configs = 3^-%d = %.2e" % (K2, float(3.0 ** (-K2))))
    print("     adequacy bar K >= 10 : %s" % ("MET" if K2 >= 10 else "NOT MET"))
    # per-B breakdown of the m=-2 cell, mandated by section 4
    res_rows = [r for r in h2 if cubic_class(r[2], r[3]) == 1]
    perB = {}
    for r in res_rows:
        perB[r[2]] = perB.get(r[2], 0) + 1
    print("     MANDATED per-B breakdown of the cubic-residue (m=-2) cell: %d rows, by B: %s"
          % (len(res_rows), perB))
    nonres = len(h2) - len(res_rows)
    print("     non-residue (m=1) cell: %d rows over %d distinct primes"
          % (nonres, len(set(r[3] for r in h2 if cubic_class(r[2], r[3]) != 1))))

    # ---- H2b rider
    grp = {}
    for r in h2:
        grp.setdefault((r[3], cubic_class(r[2], r[3])), []).append((quad_class(r[2], r[3]), r[6], r[2]))
    h2b_tested = [k for k, v in grp.items() if len(set(q for q, m, B in v)) > 1]
    h2b_viol = [(k, v) for k, v in grp.items() if len(set(m for q, m, B in v)) > 1]
    print("  H2b: within p = 7 mod 12, m depends on B ONLY through the cubic character")
    print("     configs that actually test it (same p, same cubic class, differing quad class) = %d"
          % len(h2b_tested))
    print("     violations (same (p,cubic class) but differing m) = %s"
          % (h2b_viol if h2b_viol else "NONE"))
    print("     PRE-DECLARED UNDERPOWERED (bar is K>=10). Report as 'consistent, K=%d', never as"
          % len(h2b_tested))
    print("     confirmed independence.")
    print()

    # ---- section 9 covariate grid, printed whenever anything fails
    if h1_viol or h2_viol:
        print("=" * 118)
        print("SECTION 9 PARTIAL-RATE GRID (printed BEFORE any explanation; no other covariate allowed)")
        print("=" * 118)
        print("  %-4s %-6s %-6s %-12s %-12s %-6s %-8s" %
              ("B", "p", "p%12", "cubic class", "quad class", "gcd", "m"))
        for r in cm:
            lab, isCM, B, p, b1, b2, m, mB, ok = r
            cc = cubic_class(B, p) if p % 3 == 1 else "-"
            print("  %-4d %-6d %-6d %-12s %-12s %-6d %-8s" %
                  (B, p, p % 12, cc, quad_class(B, p), gcd(12, p - 1), m))
        print("  STOP. No covariate outside this grid may be introduced in this run.")
        print()

    # ---- exploratory arm
    print("=" * 118)
    print("EXPLORATORY -- no prediction (non-CM cubics).  Recorded only; no rule, no significance.")
    print("=" * 118)
    for r in rows:
        if not r[1]:
            print("  %-14s p=%-5d p%%12=%-3d m=%-4s angles(pi) = %s"
                  % (r[0], r[3], r[3] % 12, r[6], angles_str(r[6])))
    print()

    # ---- pre-committed conclusion selector
    print("=" * 118)
    print("PRE-COMMITMENT TABLE (section 10) -- selected row")
    print("=" * 118)
    if not h1_viol and not h2_viol:
        print("  ROW 1: control passed; H1 and H2 both hold on every out-of-sample row.")
        print("  [EMPIRICAL] characterization, scoped to: 6 cubics / p=3 mod 4 / %d<p<%d."
              % (WIN_LO, WIN_HI))
        print("  NOT transferred to p = 2^256-2^32-977; the mu4 argument covers b1=0 only, NOT m.")
    elif h1_viol and h2_viol:
        print("  ROW 4: both H1 and H2 falsified as stated.  Grid printed above.  Not a closure.")
    elif h2_viol:
        print("  ROW 2: H2 FALSIFIED as stated; H1 reported on its own arm.  Grid printed above.")
    else:
        print("  ROW 3: H1 FALSIFIED as stated; H2 adjudicated independently.  Grid printed above.")
    print("  Output type: CHARACTERIZATION of which individual eigenvalue occurs under which")
    print("  arithmetic condition.  No ECDLP / secp256k1 / security verdict is made or implied.")
    print("  wall time %.1f s" % (time.time() - t0))
    print("=" * 118)


main()
