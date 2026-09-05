#!/usr/bin/env python3
"""
twist_chirality_arm3_v1.py -- ARM III of PREREG_twist_sum_B_closedform_v1.md.

Question: is sign(FLD) (and sign(B)) a property of the IDEAL (pi_p) -- and does it FLIP when the
ideal is replaced by its conjugate (pi_p-bar)?  The standing law sign(FLD) = -chi2(M) is verified
54/54 but relates two quantities that SHARE a sign convention inside the code path, so it may be a
convention rather than an identity.  One experiment decides it.

Run order (prereg section 11): Arm III runs FIRST; every orientation-carrying feature of Arms I/II
is inadmissible until this returns.

Exact integers / Fractions only.  No float anywhere.

Structure:
  * build_from_basis(p, R1, R2)  -- PLUMBING-ONLY refactor of _sigma_chi2_scan_v1.build.  The
    bodies of eis / om2 / reduce_P / the multi-probe beta calibration / eps are copied verbatim;
    the ONLY change is that (R1, R2) arrive as parameters instead of from reduced_basis(p).
    Regression check REG (prereg 7.3 step 3): build_from_basis(p, *reduced_basis(p)) must
    reproduce _twist_split_B_v1.run's (FLD, A, B, NE, NW) at every prime in scope.
  * control G (prereg 3.2)   -- the <=8 re-presentations (+-R1,+-R2), (+-R2,+-R1) of the SAME
    lattice.  If sign(FLD) varies inside G, Arm III is answered before conjugation: outcome III-e.
  * conjugation (prereg 7.2) -- conj(a,b) = (a-b, -b), det -> -det.
  * planted controls (prereg 4.3): M must FLIP, and beta' != beta with beta*beta' = 1 mod p;
    L, enorm(R1), |FLD| must NOT flip.  Failure => arm halts, no interpretation.
"""
import sys
import time
from fractions import Fraction as Fr
from sympy import isprime, primitive_root

from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm, gauss_reduce
from _sigma_chi2_scan_v1 import chi2_table

# ---------------------------------------------------------------- plumbing refactor


def build_from_basis(p, R1, R2):
    """Verbatim body of _sigma_chi2_scan_v1.build with (R1, R2) as parameters.
    Only the first two lines of the original (the reduced_basis call) are replaced."""
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def eis(X):
        X %= p
        c1 = rdiv(X * R2[1], DET)
        c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def om2(w):
        u, v = w
        return (v - u, -u)

    def reduce_P(a, b):
        c1 = rdiv(a * R2[1] - b * R2[0], DET)
        c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))

    g = primitive_root(p)
    b1 = pow(g, (p - 1) // 3, p)
    b2 = pow(b1, 2, p)
    probes = [x for x in range(1, min(p, 40))]
    ok1 = all(eis(b1 * x % p) == reduce_P(*om2(eis(x))) for x in probes)
    ok2 = all(eis(b2 * x % p) == reduce_P(*om2(eis(x))) for x in probes)
    if ok1 == ok2:
        return None                      # ambiguous calibration: caller records and skips
    beta = b1 if ok1 else b2

    def eps(X):
        U0 = eis(X)
        U1 = eis((beta * X) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0):
            return 0
        if c in (tuple(R1), tuple(R2), (-R1[0], -R1[1]), (-R2[0], -R2[1])):
            return 1
        return 2

    return eis, eps, beta, R1, R2, DET


def sigma_both(p, eis, eps, R1, R2, DET):
    """sigma_fn's 100%-agreement pre-flight, but reporting BOTH orientations (prereg 7.4).
    Returns (sig, orient, n_pass, passers). n_pass == 2 is the gauge hole and must be disclosed."""
    def co(w):
        a, b = w
        return Fr(a * R2[1] - b * R2[0], DET), Fr(b * R1[0] - a * R1[1], DET)

    passers = []
    for cand in ('-', '+'):
        ok = True
        for x in range(p):
            u, v = co(eis(x))
            s = (u - v) if cand == '-' else (u + v)
            if (abs(s) > Fr(1, 2)) != (eps(x) != 0):
                ok = False
                break
        if ok:
            passers.append(cand)
    if not passers:
        return None, None, 0, passers
    cand = passers[0]

    def sig(x, cand=cand):
        u, v = co(eis(x))
        s = (u - v) if cand == '-' else (u + v)
        if abs(s) <= Fr(1, 2):
            return 0
        return 1 if s > 0 else -1

    return sig, cand, len(passers), passers


def split_sums(p, chi2, sig):
    """A / B / FLD / CRV / NE / NW -- the unmodified _twist_split_B_v1.run body."""
    A = B = 0
    NE = NW = 0
    for x in range(p):
        w = chi2(((x * x % p) * x + 7) % p)
        s = sig(x)
        if s == 0:
            continue
        v = s * chi2(x)
        if w == 1:
            A += v
            NE += 1
        elif w == -1:
            B += v
            NW += 1
    return {'A': A, 'B': B, 'FLD': A + B, 'CRV': A - B, 'NE': NE // 3, 'NW': NW // 3}


# ---------------------------------------------------------------- lattice / CM bookkeeping

def mulw(w):
    """multiplication by omega on Z[omega] in (a,b) <-> a + b*omega coordinates:
       omega*(a + b w) = -b + (a-b) w."""
    a, b = w
    return (-b, a - b)


def conj(w):
    """conj(a + b w) = a + b w-bar = (a - b) - b w."""
    a, b = w
    return (a - b, -b)


def LM_from_lattice(p, R1):
    """(L, M) with 4p = L^2 + 27 M^2, L = 1 mod 3.  Derived from the generator actually used by
    sigma (R1 is a shortest vector of the ideal, hence an associate of pi_p).  M's SIGN is the
    free chirality bit; L is pinned by L = 1 mod 3."""
    cands = []
    w = tuple(R1)
    for _ in range(3):
        for s in (1, -1):
            a, b = s * w[0], s * w[1]
            if b % 3 == 0:
                cands.append((a, b))
        w = mulw(w)
    if not cands:
        return None
    out = []
    for a, b in cands:
        M = b // 3
        L = 2 * a - b
        assert L * L + 27 * M * M == 4 * p, f"4p = L^2+27M^2 failed at p={p}"
        if L % 3 == 1 % 3:
            out.append((L, M))
    if len(out) != 1:
        return None
    return out[0]


def gauge_orbit(R1, R2):
    """the <=8 re-presentations of the SAME lattice: (+-R1,+-R2) and (+-R2,+-R1)."""
    out = []
    for (X, Y) in ((R1, R2), (R2, R1)):
        for sx in (1, -1):
            for sy in (1, -1):
                out.append(((sx * X[0], sx * X[1]), (sy * Y[0], sy * Y[1])))
    return out


def evaluate(p, chi2, R1, R2):
    """full pipeline on one basis presentation.  Returns None if beta calibration is ambiguous
    or no orientation passes."""
    b = build_from_basis(p, R1, R2)
    if b is None:
        return {'FAIL': 'beta-ambiguous'}
    eis, eps, beta, _, _, DET = b
    sig, orient, npass, passers = sigma_both(p, eis, eps, R1, R2, DET)
    if sig is None:
        return {'FAIL': 'no-orientation'}
    r = split_sums(p, chi2, sig)
    r.update({'beta': beta, 'orient': orient, 'npass': npass, 'DET': DET})
    return r


# ---------------------------------------------------------------- the arm

def run_prime(p, chi2):
    R1, R2 = reduced_basis(p)
    base = evaluate(p, chi2, R1, R2)
    if 'FAIL' in base:
        return {'p': p, 'FAIL': base['FAIL']}
    lm = LM_from_lattice(p, R1)
    if lm is None:
        return {'p': p, 'FAIL': 'LM-ambiguous'}
    L, M = lm

    # ---- control G: the gauge orbit of the SAME ideal (prereg 3.2)
    g_fld, g_B, g_npass, g_fail = [], [], [], 0
    for (X, Y) in gauge_orbit(R1, R2):
        if X[0] * Y[1] - X[1] * Y[0] == 0:
            continue
        rg = evaluate(p, chi2, X, Y)
        if 'FAIL' in rg:
            g_fail += 1
            continue
        g_fld.append(rg['FLD'])
        g_B.append(rg['B'])
        g_npass.append(rg['npass'])

    # ---- conjugation (prereg 7.2/7.3)
    R1c, R2c = conj(R1), conj(R2)
    DETc = R1c[0] * R2c[1] - R1c[1] * R2c[0]
    DET = R1[0] * R2[1] - R1[1] * R2[0]
    assert DETc == -DET, f"conj det parity failed at p={p}"
    assert enorm(R1c) == enorm(R1) and enorm(R2c) == enorm(R2), f"conj not an isometry at p={p}"
    conjr = evaluate(p, chi2, R1c, R2c)
    if 'FAIL' in conjr:
        return {'p': p, 'FAIL': 'conj:' + conjr['FAIL']}
    lmc = LM_from_lattice(p, R1c)
    if lmc is None:
        return {'p': p, 'FAIL': 'LM-ambiguous-conj'}
    Lc, Mc = lmc

    # gauss-reduction status of the conjugate basis (reported, not asserted)
    gr = gauss_reduce(R1c, R2c)
    conj_reduced = set(map(tuple, gr)) == {tuple(R1c), tuple(R2c)}

    return {
        'p': p, 'L': L, 'M': M, 'Lc': Lc, 'Mc': Mc,
        'FLD': base['FLD'], 'B': base['B'], 'A': base['A'], 'CRV': base['CRV'],
        'NE': base['NE'], 'NW': base['NW'],
        'FLDc': conjr['FLD'], 'Bc': conjr['B'], 'Ac': conjr['A'], 'CRVc': conjr['CRV'],
        'beta': base['beta'], 'betac': conjr['beta'],
        'orient': base['orient'], 'orientc': conjr['orient'],
        'npass': base['npass'], 'npassc': conjr['npass'],
        'g_fld_set': sorted(set(g_fld)), 'g_B_set': sorted(set(g_B)),
        'g_npass_max': max(g_npass) if g_npass else None, 'g_fail': g_fail,
        'g_n': len(g_fld), 'conj_reduced': conj_reduced,
        'enorm_R1': enorm(R1),
    }


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 2500
    t0 = time.time()
    rows, fails = [], []
    for p in range(lo, hi):
        if p % 24 != 19 or not isprime(p):
            continue                      # SCOPE_III = p = 19 mod 24  (prereg 6.4)
        chi2 = chi2_table(p)
        r = run_prime(p, chi2)
        if 'FAIL' in r:
            fails.append(r)
            continue
        rows.append(r)

    print(f"# ARM III  chirality of sign(FLD)/sign(B).  SCOPE_III: p = 19 mod 24, p in [{lo},{hi}).")
    print(f"# primes evaluated = {len(rows)}   failed/excluded = {len(fails)}")
    if fails:
        print("# EXCLUSIONS (disclosed, prereg 7.4):")
        for f in fails:
            print(f"#   p={f['p']:>6}  {f['FAIL']}")
    print()
    hdr = (f"# {'p':>5} {'L':>5} {'M':>5} {'Mc':>5} {'Lc':>5} {'FLD':>5} {'FLDc':>5} {'B':>5} "
           f"{'Bc':>5} {'A':>5} {'Ac':>5} {'or':>3} {'orc':>3} {'np':>3} {'npc':>3} "
           f"{'|G|':>4} {'Gflds':>14} {'GBs':>14}")
    print(hdr)
    n_flip_fld = n_flip_B = n_flip_A = 0
    n_same_fld = n_same_B = 0
    cell = {}
    gauge_varies = []
    ctrl_M = ctrl_L = ctrl_absFLD = ctrl_beta = 0
    for r in rows:
        fF = (r['FLDc'] == -r['FLD']) and r['FLD'] != 0
        sF = (r['FLDc'] == r['FLD']) and r['FLD'] != 0
        fB = (r['Bc'] == -r['B']) and r['B'] != 0
        sB = (r['Bc'] == r['B']) and r['B'] != 0
        fA = (r['Ac'] == -r['A']) and r['A'] != 0
        n_flip_fld += fF; n_same_fld += sF
        n_flip_B += fB; n_same_B += sB
        n_flip_A += fA
        key = ('flip' if fF else ('same' if sF else 'other'),
               'flip' if fB else ('same' if sB else 'other'))
        cell[key] = cell.get(key, 0) + 1
        # planted controls (prereg 4.3)
        ctrl_M += (r['Mc'] == -r['M'])
        ctrl_L += (r['Lc'] == r['L'])
        ctrl_absFLD += (abs(r['FLDc']) == abs(r['FLD']))
        ctrl_beta += (r['betac'] != r['beta'] and (r['beta'] * r['betac']) % r['p'] == 1)
        if len(r['g_fld_set']) > 1:
            gauge_varies.append(r['p'])
        print(f"  {r['p']:>5} {r['L']:>5} {r['M']:>5} {r['Mc']:>5} {r['Lc']:>5} {r['FLD']:>5} "
              f"{r['FLDc']:>5} {r['B']:>5} {r['Bc']:>5} {r['A']:>5} {r['Ac']:>5} "
              f"{r['orient']:>3} {r['orientc']:>3} {r['npass']:>3} {r['npassc']:>3} "
              f"{r['g_n']:>4} {str(r['g_fld_set']):>14} {str(r['g_B_set']):>14}")

    N = len(rows)
    print()
    print("## PLANTED CONTROLS (prereg 4.3) -- all must fire; otherwise the arm halts")
    print(f"  chirality-ODD  M' = -M                   : {ctrl_M}/{N}")
    print(f"  chirality-ODD  beta' != beta, beta*beta'=1: {ctrl_beta}/{N}")
    print(f"  chirality-EVEN L' = L                    : {ctrl_L}/{N}")
    print(f"  chirality-EVEN |FLD'| = |FLD|            : {ctrl_absFLD}/{N}")
    print(f"  enorm(R1) == p                           : "
          f"{sum(1 for r in rows if r['enorm_R1'] == r['p'])}/{N}")
    print()
    print("## CONTROL G -- gauge orbit of the SAME ideal (prereg 3.2)")
    print(f"  primes where sign(FLD) varies inside G   : {len(gauge_varies)}/{N} {gauge_varies[:12]}")
    print(f"  primes where |G| < 8 (degenerate)        : "
          f"{sum(1 for r in rows if r['g_n'] < 8)}/{N}")
    print(f"  max orientations passing pre-flight      : "
          f"{max([r['g_npass_max'] for r in rows if r['g_npass_max']] + [0])} (2 = the gauge hole)")
    print(f"  conj basis already gauss-reduced         : "
          f"{sum(1 for r in rows if r['conj_reduced'])}/{N}")
    print()
    print("## PRIMARY STATISTIC T3 (prereg 2, Arm III)")
    print(f"  T3 = #(FLD flips AND B flips)            : "
          f"{cell.get(('flip','flip'),0)}/{N}")
    print(f"  2x2 table (FLD, B):")
    for k in sorted(cell):
        print(f"     FLD={k[0]:<5} B={k[1]:<5} : {cell[k]}")
    print(f"  A flips: {n_flip_A}/{N}   FLD flips: {n_flip_fld}/{N} (same {n_same_fld})   "
          f"B flips: {n_flip_B}/{N} (same {n_same_B})")
    print()
    print("## the standing sign law, both chiralities")
    def chi2v(a, p):
        a %= p
        if a == 0: return 0
        return 1 if pow(a, (p - 1) // 2, p) == 1 else -1
    law = sum(1 for r in rows
              if (1 if r['FLD'] > 0 else -1) == -chi2v(r['M'], r['p']))
    lawc = sum(1 for r in rows
               if (1 if r['FLDc'] > 0 else -1) == -chi2v(r['Mc'], r['p']))
    print(f"  sign(FLD)  = -chi2(M)   : {law}/{N}")
    print(f"  sign(FLD') = -chi2(M')  : {lawc}/{N}")
    print(f"\n# elapsed {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
