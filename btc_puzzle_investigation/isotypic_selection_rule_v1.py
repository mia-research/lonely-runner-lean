#!/usr/bin/env python3
r"""
isotypic_selection_rule_v1.py -- the mu6 bigrading of the readout algebra of E: y^2=x^3+7.

PRE-REGISTERED in this session (experiment-designer spec, 2026-07-17). Object-level, exact,
no float in the signal path (integer Z[omega] throughout; Fraction only for final reporting).

OBJECT. The point set E(F_p)\{O} with its Aut(E)=mu6 action, and the exact pairing
    Sig(F,G) := sum_{P != O} F(P) conj(G(P))   in Z[omega].
G (a generator) is NOT in the object: every readout is a function of (x,y), and mu6 acts
directly on points. No DLP, no scalar_mul, no lambda calibration.

  [-1] : (x,y) -> (x,-y)          order 2, generator of mu2
  [lam]: (x,y) -> (beta x, y)     order 3, generator of mu3   (beta^3=1 mod p)
mu6 = mu2 x mu3 acts FREELY on E\{O} when n=#E is prime (no 2-torsion since n odd; no
fixed point of [lam] since x=beta*x => x=0 => y^2=7, and that point has order... see
assertion FREE below -- we verify freeness directly rather than argue it).

BIDEGREE. F has bidegree (j,k) in Z/2 x Z/3 iff
    F([-1]P) = (-1)^j F(P)  and  F([lam]P) = omega^k F(P)   for ALL P != O.
CLAIM S (theorem): Sig(F,G) = 0 whenever bidegree(F) != bidegree(G).
    Proof: reindex P -> uP for u in mu6. Sig = chi_F(u) conj(chi_G(u)) Sig for every u.
    If the characters differ, some u gives a factor != 1, forcing Sig = 0. QED.
The RUN cannot upgrade this tag -- it checks the implementation and the bidegree
assignments, not the theorem (see spec Part 1 / outcome O1).

THE FIELD/CURVE SPLIT (mandated for every j=0 pairing; the central proxy guard).
For F,G functions of x alone, #{y : y^2=x^3+7} = 1 + chi2(x^3+7), so
    Sig(F,G) = sum_x F conj(G)          +  sum_x F conj(G) chi2(x^3+7)
             = FIELD (pure F_p lattice)  +  CURVE (Weil-scale character sum)
Reporting the total as one number attributes a LATTICE fact to CURVE arithmetic.
Never report the total alone for j=0.

Usage:  python3 isotypic_selection_rule_v1.py [--quick]
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime, primitive_root
from sympy.ntheory.residue_ntheory import sqrt_mod

from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm, sextant

# ---------------------------------------------------------------- Z[omega] exact arithmetic
# element (a,b) means a + b*omega ; omega^2 = -1 - omega
OM = [(1, 0), (0, 1), (-1, -1)]          # omega^0, omega^1, omega^2
ZETA6 = (1, 1)                            # zeta6 = 1 + omega = -omega^2
Z0, Z1 = (0, 0), (1, 0)

def zmul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)

def zconj(z):
    a, b = z
    return (a - b, -b)

def znorm(z):                              # |z|^2, exact, in Z
    a, b = z
    return a * a - a * b + b * b

def zadd(z, w): return (z[0] + w[0], z[1] + w[1])
def zscale(z, k): return (z[0] * k, z[1] * k)
def zpow_om(i): return OM[i % 3]

def zeta6_pow(e):
    z = Z1
    for _ in range(e % 6):
        z = zmul(z, ZETA6)
    return z

# ---------------------------------------------------------------- lattice / lift machinery
def build_lift(p):
    """Return (eis, eps, beta, R1, R2, DET). eis in the (1,omega) basis. beta calibrated so
    that eis(beta*X) == omega^2 * eis(X) reduced mod L  (this is int1_frame_operator_v1's
    calibration, replicated here so we also get beta out)."""
    R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def eis(X):
        X %= p
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def om2(w): u, v = w; return (v - u, -u)          # multiplication by omega^2 in (1,omega)
    def reduce_P(a, b):
        c1 = rdiv(a * R2[1] - b * R2[0], DET); c2 = rdiv(b * R1[0] - a * R1[1], DET)
        return (a - (c1 * R1[0] + c2 * R2[0]), b - (c1 * R1[1] + c2 * R2[1]))

    # the two nontrivial cube roots of 1 mod p
    g = primitive_root(p)
    b1 = pow(g, (p - 1) // 3, p); b2 = pow(b1, 2, p)
    # BETA CALIBRATION -- fixed here; do NOT copy int1_frame_operator_v1.py:41, which
    # calibrates on the single hardcoded probe x=12345. Since 12345 = 3*5*823, at p=823 the
    # probe is x=0, the test degenerates to (0,0)==(0,0), and b1 is returned untested -- the
    # WRONG root there (exact omega^2 relation 0/822, eps==2 for 822/823). Verified 2026-07-17.
    probes = [x for x in range(1, min(p, 40))]
    ok1 = all(eis(b1 * x % p) == reduce_P(*om2(eis(x))) for x in probes)
    ok2 = all(eis(b2 * x % p) == reduce_P(*om2(eis(x))) for x in probes)
    assert ok1 != ok2, f"beta calibration ambiguous at p={p}: ok1={ok1} ok2={ok2}"
    beta = b1 if ok1 else b2

    def eps(X):
        U0 = eis(X); U1 = eis((beta * X) % p)
        c = (U1[0] - om2(U0)[0], U1[1] - om2(U0)[1])
        if c == (0, 0): return 0
        if c in (tuple(R1), tuple(R2), (-R1[0], -R1[1]), (-R2[0], -R2[1])): return 1
        return 2
    return eis, eps, beta, R1, R2, DET

def coeffs_R(w, R1, R2, DET):
    """(R1,R2)-basis coordinates of w=(a,b) in the (1,omega) plane. Exact Fractions."""
    a, b = w
    u = Fr(a * R2[1] - b * R2[0], DET)
    v = Fr(b * R1[0] - a * R1[1], DET)
    return u, v

# ---------------------------------------------------------------- curve
def chi2_table(p):
    qr = bytearray(p)
    for i in range(1, (p - 1) // 2 + 1):
        qr[i * i % p] = 1
    def chi2(v):
        v %= p
        if v == 0: return 0
        return 1 if qr[v] else -1
    return chi2

def curve_order(p, chi2):
    s = 0
    for x in range(p):
        s += chi2((x * x % p) * x % p + 7)
    return p + 1 + s

def points_of(p, chi2):
    pts = []
    for x in range(p):
        rhs = ((x * x % p) * x + 7) % p
        c = chi2(rhs)
        if c == 0:
            y = sqrt_mod(rhs, p)
            if y is not None: pts.append((x, y % p))
        elif c == 1:
            y = sqrt_mod(rhs, p)
            y %= p
            pts.append((x, y)); pts.append((x, (p - y) % p))
    return pts

# ---------------------------------------------------------------- readouts
def make_readouts(p, eis, eps, beta, R1, R2, DET, orient):
    """Every readout returns an exact Z[omega] element (integer coords).
    orient in {'-','+'} selects sigma's cap orientation |u-v| vs |u+v| (pre-flight asserted).
    NOTE nrm is returned as the INTEGER enorm(eis(x)) = p * (norm band s); positive scaling
    does not affect zero-ness or bidegree."""
    chi2 = chi2_table(p)
    g = primitive_root(p)
    # discrete-log table for F_p^* (exact, O(p))
    ind = [0] * p
    a = 1
    for i in range(p - 1):
        ind[a] = i
        a = a * g % p

    half = (p - 1) // 2

    def R_x(P):    return (P[0], 0)
    def R_ynn(P):  return (P[1], 0)
    def R_yctr(P): return (P[1] if P[1] <= half else P[1] - p, 0)
    def R_sy(P):   return (1, 0) if P[1] <= half else (-1, 0)
    def R_xyctr(P):
        yc = P[1] if P[1] <= half else P[1] - p
        return (P[0] * yc, 0)
    def R_chi2x(P): return (chi2(P[0]), 0)
    def R_chi2y(P): return (chi2(P[1]), 0)
    def R_chi3x(P):
        if P[0] % p == 0: return Z0
        return zpow_om(ind[P[0] % p] % 3)
    def R_chi6x(P):
        if P[0] % p == 0: return Z0
        return zeta6_pow(ind[P[0] % p] % 6)
    def R_eisx(P): return eis(P[0])
    def R_nrm(P):  return (enorm(eis(P[0])), 0)
    def R_sxtz6(P):
        u, v = eis(P[0])
        return zeta6_pow(sextant(u, v))
    def R_eps(P):  return (eps(P[0]), 0)
    def R_sigma(P):
        u, v = coeffs_R(eis(P[0]), R1, R2, DET)
        s = (u - v) if orient == '-' else (u + v)
        if abs(s) <= Fr(1, 2): return Z0
        return (1, 0) if s > 0 else (-1, 0)
    def R_one(P):  return Z1

    return [
        ('one',    R_one),   ('x',      R_x),     ('y_nn',  R_ynn),   ('y_ctr', R_yctr),
        ('s_y',    R_sy),    ('xy_ctr', R_xyctr), ('chi2x', R_chi2x), ('chi2y', R_chi2y),
        ('chi3x',  R_chi3x), ('chi6x',  R_chi6x), ('eisx',  R_eisx),  ('nrm',   R_nrm),
        ('sxt_z6', R_sxtz6), ('eps',    R_eps),   ('sigma', R_sigma),
    ]

# class membership for the tautology audit (spec 1b)
CLASS = {
    'one': 'R0',
    'x': 'X', 'xy_ctr': 'X',
    'y_nn': 'Y', 'y_ctr': 'Y', 's_y': 'Y', 'chi2y': 'Y',
    'chi2x': 'M', 'chi3x': 'M', 'chi6x': 'M',
    'eisx': 'L', 'nrm': 'L', 'sxt_z6': 'L', 'eps': 'L', 'sigma': 'L',
}

# ---------------------------------------------------------------- mu6 action
def act(P, e, i, p, beta_pows):
    x, y = P
    x2 = x * beta_pows[i] % p
    y2 = y if e == 0 else (p - y) % p
    return (x2, y2)

def chi_jk(j, k, e, i):
    return zscale(zpow_om(k * i), (-1) ** (j * e))

# ---------------------------------------------------------------- Part 1: bidegree + energy
def part1(p, pts, R, beta_pows):
    """Exact defect counts D_F(j,k) over the FULL point set, and isotypic energies."""
    table = {}
    for name, F in R:
        vals = {}
        for P in pts:
            for e in (0, 1):
                for i in (0, 1, 2):
                    vals[(P, e, i)] = F(act(P, e, i, p, beta_pows))
        D = {}
        for j in (0, 1):
            for k in (0, 1, 2):
                d = 0
                for P in pts:
                    f0 = vals[(P, 0, 0)]
                    if vals[(P, 1, 0)] != zscale(f0, (-1) ** j) or vals[(P, 0, 1)] != zmul(zpow_om(k), f0):
                        d += 1
                D[(j, k)] = d
        # isotypic energies: 6*F_{j,k}(P) kept integral; E scaled back by 36
        E = {}
        for j in (0, 1):
            for k in (0, 1, 2):
                tot = 0
                for P in pts:
                    acc = Z0
                    for e in (0, 1):
                        for i in (0, 1, 2):
                            acc = zadd(acc, zmul(zconj(chi_jk(j, k, e, i)), vals[(P, e, i)]))
                    tot += znorm(acc)
                E[(j, k)] = Fr(tot, 36)
        table[name] = (D, E)
    return table

def bidegree_of(D):
    hits = [jk for jk, d in D.items() if d == 0]
    return hits[0] if len(hits) == 1 else None

# ---------------------------------------------------------------- Part 1: Gram + split
def gram(p, pts, R, bideg, chi2):
    """Direct Sig(F,G) over all P != O -- NOT via orbits (that would assume Claim S)."""
    names = [n for n, _ in R]
    vals = {n: [F(P) for P in pts] for n, F in R}
    S = {}
    for a in range(len(names)):
        for b in range(len(names)):
            na, nb = names[a], names[b]
            acc = Z0
            va, vb = vals[na], vals[nb]
            for t in range(len(pts)):
                acc = zadd(acc, zmul(va[t], zconj(vb[t])))
            S[(na, nb)] = acc
    return S

def field_curve_split(p, R, chi2, names_j0):
    """For readouts that are functions of x alone: Sig = FIELD + CURVE, computed by summing
    over x in F_p with multiplicity 1 and chi2(x^3+7) respectively."""
    Rd = dict(R)
    xs = list(range(p))
    cache = {}
    for n in names_j0:
        F = Rd[n]
        cache[n] = [F((x, 0)) for x in xs]      # y is unused by these readouts
    w = [chi2(((x * x % p) * x + 7) % p) for x in xs]
    out = {}
    for a in names_j0:
        for b in names_j0:
            fa, fb = cache[a], cache[b]
            fld = Z0; crv = Z0
            for t in range(p):
                z = zmul(fa[t], zconj(fb[t]))
                fld = zadd(fld, z)
                crv = zadd(crv, zscale(z, w[t]))
            out[(a, b)] = (fld, crv)
    return out

# ---------------------------------------------------------------- orbits + controls
def orbits_of(p, pts, beta_pows):
    seen = set(); reps = []
    ptset = set(pts)
    for P in pts:
        if P in seen: continue
        orb = set()
        for e in (0, 1):
            for i in (0, 1, 2):
                orb.add(act(P, e, i, p, beta_pows))
        assert len(orb) == 6, f"mu6 action NOT free at {P}: orbit size {len(orb)}"
        assert orb <= ptset, "orbit left the point set"
        seen |= orb
        reps.append(min(orb))
    return reps

def controls(p, pts, reps, R, beta_pows):
    """PC-1: T(s_y,s_y) == m. PC-2: T(s_y, s_y*h) == floor(m/2) exactly, h = orbit indicator
    (bidegree (0,0) by construction), so s_y*h matches s_y at (1,0) -- a KNOWN nonzero at
    matching bidegree. If PC-2 does not fire, every zero in this run is uninformative."""
    Rd = dict(R)
    sy = Rd['s_y']
    m = len(reps)
    order = {rep: idx for idx, rep in enumerate(sorted(reps))}
    cut = m // 2
    def h_of(P):
        # constant on orbits: find the orbit rep of P
        orb = min(act(P, e, i, p, beta_pows) for e in (0, 1) for i in (0, 1, 2))
        return 1 if order[orb] < cut else 0
    T11 = sum(znorm(sy(rep)) for rep in reps)
    T12 = Z0
    for rep in reps:
        g = zscale(sy(rep), h_of(rep))
        T12 = zadd(T12, zmul(sy(rep), zconj(g)))
    return m, T11, T12, cut

# ---------------------------------------------------------------- prime selection
def select_primes(lo, per_class, classes=(1, 7, 13, 19, 25, 31), cap=200000):
    """Deterministic rule, fixed pre-run: smallest `per_class` primes p > lo with p mod 36 in
    `classes`, p not in {2,3,7}, and n=#E(F_p) PRIME. 'n prime' IS a filter -- skipped counts
    are reported per class (spec: SILENT-FILTER DISCLOSURE)."""
    found = {c: [] for c in classes}
    skipped = {c: 0 for c in classes}
    p = lo + 1
    while any(len(v) < per_class for v in found.values()) and p < cap:
        c = p % 36
        if c in classes and len(found[c]) < per_class and isprime(p) and p not in (2, 3, 7):
            chi2 = chi2_table(p)
            n = curve_order(p, chi2)
            if isprime(n):
                found[c].append((p, n))
            else:
                skipped[c] += 1
        p += 1
    return found, skipped

# ---------------------------------------------------------------- driver
def run_prime(p, n, verbose=True):
    chi2 = chi2_table(p)
    eis, eps, beta, R1, R2, DET = build_lift(p)
    beta_pows = [1, beta % p, beta * beta % p]

    # --- pre-flight: sigma orientation, 100% agreement with eps != 0 (NOT a majority vote)
    orient = None
    for cand in ('-', '+'):
        ok = True
        for x in range(p):
            u, v = coeffs_R(eis(x), R1, R2, DET)
            s = (u - v) if cand == '-' else (u + v)
            if (abs(s) > Fr(1, 2)) != (eps(x) != 0):
                ok = False; break
        if ok:
            orient = cand; break
    if orient is None:
        return {'p': p, 'FAIL': 'no sigma orientation agrees with eps on all x'}

    n_eps2 = sum(1 for x in range(p) if eps(x) == 2)

    pts = points_of(p, chi2)
    assert len(pts) == n - 1, f"point count {len(pts)} != n-1 = {n-1}"

    R = make_readouts(p, eis, eps, beta, R1, R2, DET, orient)
    reps = orbits_of(p, pts, beta_pows)          # asserts FREENESS
    m, T11, T12, cut = controls(p, pts, reps, R, beta_pows)

    t1 = part1(p, pts, R, beta_pows)
    bideg = {nm: bidegree_of(D) for nm, (D, E) in t1.items()}
    S = gram(p, pts, R, bideg, chi2)

    j0 = [nm for nm, _ in R if bideg.get(nm) is not None and bideg[nm][0] == 0
          and nm in ('one', 'chi2x', 'chi3x', 'chi6x', 'eisx', 'nrm', 'sxt_z6', 'eps', 'sigma')]
    split = field_curve_split(p, R, chi2, j0)

    # --- Part 2B: the sigma conservation, three exact integers
    sig = dict(R)['sigma']
    B1 = sum(sig((x, 0))[0] for x in range(1, p))                      # field sum over F_p^*
    B2 = sum(sig(P)[0] for P in pts)                                   # curve sum
    C = sum(sig((x, 0))[0] * chi2(((x * x % p) * x + 7) % p) for x in range(p))
    return {
        'p': p, 'n': n, 'm': m, 'm_odd': m % 2, 'pmod36': p % 36, 'pmod4': p % 4,
        'pmod9': p % 9, 'orient': orient, 'n_eps2': n_eps2, 'beta': beta,
        'R1': tuple(R1), 'R2': tuple(R2),
        'PC1': (T11, m), 'PC2': (T12, cut),
        'bideg': bideg, 'part1': t1, 'gram': S, 'split': split,
        'B1': B1, 'B2': B2, 'C': C, 'names': [nm for nm, _ in R],
    }

def main():
    quick = '--quick' in sys.argv
    lo, per = (2000, 1) if quick else (10000, 2)
    found, skipped = select_primes(lo, per)
    plist = [pn for c in sorted(found) for pn in found[c]]
    print(f"# pre-registered prime list (p > {lo}, {per}/class mod 36, n prime): {[p for p,_ in plist]}")
    print(f"# skipped candidates per class (n composite): {skipped}\n")
    res = [run_prime(p, n) for p, n in plist]
    import pickle
    with open('_isotypic_v1_results.pkl', 'wb') as f:
        pickle.dump(res, f)
    print(f"# wrote _isotypic_v1_results.pkl  ({len(res)} primes)")
    return res

if __name__ == '__main__':
    main()
