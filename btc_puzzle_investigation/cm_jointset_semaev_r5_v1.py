"""
cm_jointset_semaev_r5_v1.py -- runner for PREREG_cm_jointset_semaev_r5_v1.md (S5, r=5 pure Semaev).

Primary object: Ψ5 = chi3(S5(x1..x5)) vs J=(sum d_i) mod 3, m=5 independent scalars, conditioned on the
SYMMETRIC MULTISET stratum (n0,n1,n2)=counts of chi3(x_i) (21 strata, estimable) -- NOT the unestimable
3^5=243 ordered stratum (the frontier co-arm). CM (j=0) vs matched non-CM; Delta = I(CM)-I(nonCM).

S5 = Res_X(S4(x1,x2,x3,X), S3(x4,x5,X)) as a 6x6 Sylvester determinant (deg-4 (+) deg-2), computed
EXACTLY over GF(q): S4(x1,x2,x3,X)'s deg-4-in-X coefficients by Lagrange interpolation of the
citation-verified semaev_s4 at 5 nodes, then a 6x6 Sylvester det via modular Gaussian elimination.
KAT (this session): S5 vanishes on 80/80 true 5-relations, generic-nonzero on random distinct-x tuples.

COINCIDENT-X GUARD + a CORRECTION to the frozen spec (see _v1_DEVIATIONS): the prereg's rationale
"repeated x forces a trivial curve-independent S5=0" is FALSE for ODD r=5 -- verified 4/198 (=random
rate), because 5 points cannot be tiled into disjoint cancelling pairs. The guard is KEPT as CONSTRUCTION
HYGIENE (a coincident pair feeding S3, x4=x5, zeros its leading coeff (x4-x5)^2 and degenerates the
Sylvester degree) and is applied identically to both arms (== distinct-scalar in-interval).

SIGNAL PATH exact int/GF(q). Float only as the log2 inside MI, ranked against exact integer within-
stratum permutation counts (# noqa: float). check_no_float.sh must pass.

Usage:
  python3 cm_jointset_semaev_r5_v1.py --selftest
  python3 cm_jointset_semaev_r5_v1.py --controls [--N 5000] [--R 1500]
  python3 cm_jointset_semaev_r5_v1.py --tier discovery [--N 5000] [--R 1500]
"""
from __future__ import annotations
import sys, os, math, random, hashlib, argparse, json
from fractions import Fraction
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model_curve_infra_v1 as M
from cm_jointset_ho_v1 import (Arm, build_cm_arm, build_noncm_arm, within_stratum_perm_test,
                               draw_sets, pts, interval, semaev_s4)

PREREG = "PREREG_cm_jointset_semaev_r5_v1.md"
SEED = 20260821

# ============================ S5 primitive ===================================
def _polymul_linear(poly, c0, q):
    res = [0] * (len(poly) + 1)
    for k, ak in enumerate(poly):
        res[k] = (res[k] + ak * c0) % q
        res[k + 1] = (res[k + 1] + ak) % q
    return res

def _poly_from_values(nodes, vals, q):
    """Lagrange interpolation -> coefficient list [c0..c_{n-1}] (modular inverse, no float)."""
    n = len(nodes); coeffs = [0] * n
    for i in range(n):
        num = [1]; denom = 1
        for j in range(n):
            if j == i:
                continue
            num = _polymul_linear(num, (-nodes[j]) % q, q)
            denom = denom * ((nodes[i] - nodes[j]) % q) % q
        scale = vals[i] * pow(denom % q, q - 2, q) % q
        for k in range(len(num)):
            coeffs[k] = (coeffs[k] + scale * num[k]) % q
    return coeffs

def _det_modq(Mx, q):
    """Determinant over F_q via Gaussian elimination (pow-inverse; no float, no true division)."""
    A = [row[:] for row in Mx]; n = len(A); det = 1
    for c in range(n):
        piv = None
        for r in range(c, n):
            if A[r][c] % q != 0:
                piv = r; break
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]; det = (-det) % q
        det = det * A[c][c] % q
        inv = pow(A[c][c] % q, q - 2, q)
        for r in range(c + 1, n):
            f = A[r][c] * inv % q
            if f:
                for cc in range(c, n):
                    A[r][cc] = (A[r][cc] - f * A[c][cc]) % q
    return det % q

def semaev_s5(xs, A, B, q):
    """S5(x1..x5) = Res_X(S4(x1,x2,x3,X), S3(x4,x5,X)) mod q, exact. Requires distinct x (guard)."""
    x1, x2, x3, x4, x5 = xs
    nodes = [0, 1, 2, 3, 4]
    vals = [semaev_s4(x1, x2, x3, nd, A, B, q) for nd in nodes]
    f = _poly_from_values(nodes, vals, q)                  # [f0..f4], deg 4 in X
    g2 = (x4 - x5) ** 2 % q
    g1 = (-2 * (((x4 + x5) * (x4 * x5 + A)) + 2 * B)) % q
    g0 = (((x4 * x5 - A) ** 2) - 4 * B * (x4 + x5)) % q
    fh = [f[4], f[3], f[2], f[1], f[0]]; gh = [g2, g1, g0]
    S = []
    for r in range(2):
        row = [0] * 6
        for k in range(5):
            row[r + k] = fh[k]
        S.append(row)
    for r in range(4):
        row = [0] * 6
        for k in range(3):
            row[r + k] = gh[k]
        S.append(row)
    return _det_modq(S, q)

# ============================ features =======================================
def _chi3_list(arm, P):
    return [arm.chi3x(Pi) for Pi in P]

def feat_S5(arm, d, P):
    """PRIMARY: Ψ5=chi3(S5), stratum = multiset (n0,n1,n2) of chi3(x_i)."""
    c = _chi3_list(arm, P)
    strat = (c.count(0), c.count(1), c.count(2))
    xs = [Pi[0] for Pi in P]
    return strat, M.chi3(semaev_s5(xs, arm.A, arm.B, arm.q), arm.q, arm.zeta), sum(d) % 3

def feat_S5_ordered(arm, d, P):
    """FRONTIER co-arm: same Ψ5, ordered stratum (chi3 x_i) (243)."""
    c = _chi3_list(arm, P)
    xs = [Pi[0] for Pi in P]
    return tuple(c), M.chi3(semaev_s5(xs, arm.A, arm.B, arm.q), arm.q, arm.zeta), sum(d) % 3

def feat_placebo(arm, d, P):
    """PC-PLACEBO: Ψ_pp=(sum chi3 x_i) mod 3, stratum=multiset -> a within-stratum constant, must NOT fire."""
    c = _chi3_list(arm, P)
    strat = (c.count(0), c.count(1), c.count(2))
    return strat, sum(c) % 3, sum(d) % 3

# ============================ measure / plant ================================
def _tuple_ok(P, m):
    if None in P:
        return False
    xs = [Pi[0] for Pi in P]
    return len(set(xs)) == m           # coincident-x guard (construction hygiene)

def measure(arm, featfn, N, R, rng, m=5):
    sets, ival = draw_sets(arm, m, N, rng)         # draw_sets already rejects repeated scalars
    strat = []; feat = []; targ = []
    for d in sets:
        P = pts(arm, d)
        if not _tuple_ok(P, m):
            continue
        u, fv, t = featfn(arm, d, P)
        strat.append(u); feat.append(fv); targ.append(t)
    Nn = len(strat)
    mi, p = within_stratum_perm_test(strat, feat, targ, Nn, R, rng)
    return {"mi": mi, "p": p, "s_strata": len(set(strat)), "N": Nn, "b": ival[0]}

def plant_s5(arm, N, R, rng, rho):
    """PC-S5 (must fire): mixture rho, resample d5 (real independent P5) until Ψ5==J, distinct-x."""
    b, lo, hi = interval(arm.q)
    strat = []; feat = []; targ = []; planted_feat = []; planted = 0; draws = 0
    base, _ = draw_sets(arm, 5, N, rng)
    for d in base:
        d = list(d)
        if rng.random() < rho:                                     # noqa: float
            planted += 1; hit = None
            for _try in range(120):
                d[4] = rng.randrange(lo, hi); draws += 1
                P = pts(arm, d)
                if not _tuple_ok(P, 5):
                    continue
                u, fv, t = feat_S5(arm, d, P)
                if fv == t:
                    hit = (u, fv, t); break
            if hit is None:
                d[4] = rng.randrange(lo, hi); P = pts(arm, d)
                if not _tuple_ok(P, 5):
                    continue
                u, fv, t = feat_S5(arm, d, P); hit = (u, fv, t)
            u, fv, t = hit; planted_feat.append(fv)
        else:
            P = pts(arm, d)
            if not _tuple_ok(P, 5):
                continue
            u, fv, t = feat_S5(arm, d, P)
        strat.append(u); feat.append(fv); targ.append(t)
    Nn = len(strat)
    mi, p = within_stratum_perm_test(strat, feat, targ, Nn, R, rng)
    return {"rho": rho, "mi": mi, "p": p, "distinct_planted": len(set(planted_feat)),
            "n_planted": planted, "mean_draws": Fraction(draws, max(planted, 1)), "N_eff": Nn}

def plant_grade(arm, N, R, rng, mix):
    """PC-GRADE: Ψ5_plant = J w.p. mix else uniform{0,1,2}; resolution-floor calibration."""
    sets, _ = draw_sets(arm, 5, N, rng)
    strat = []; feat = []; targ = []
    for d in sets:
        P = pts(arm, d)
        if not _tuple_ok(P, 5):
            continue
        u, _fv, t = feat_S5(arm, d, P)
        fp = t if rng.random() < mix else rng.randrange(3)         # noqa: float
        strat.append(u); feat.append(fp); targ.append(t)
    Nn = len(strat)
    mi, p = within_stratum_perm_test(strat, feat, targ, Nn, R, rng)
    return {"mix": mix, "mi": mi, "p": p, "N_eff": Nn}

# ============================ orchestration ==================================
def prereg_sha():
    try:
        return hashlib.sha256(open(PREREG, "rb").read()).hexdigest()
    except FileNotFoundError:
        return "(prereg not found)"

def load_schedule():
    return json.load(open("schedules_v1/schedule_A_joint_v1.json"))

def controls(N, R):
    rng = random.Random(SEED)
    arm = build_cm_arm(load_schedule()["discovery"][0])
    print(f"== FIRING CONTROLS (CM q={arm.q} B={arm.B} N={arm.N}) N={N} R={R} ==")
    print("  -- PC-S5 (PRIMARY, must fire at rho=0.30) --")
    for rho in (0.0, 0.15, 0.30, 0.60):                            # noqa: float
        r = plant_s5(arm, N, R, rng, rho)
        print(f"     rho={rho:<4} mi={r['mi']:+.4f} p={float(r['p']):.4f} "         # noqa: float
              f"distinct_planted={r['distinct_planted']} N_eff={r['N_eff']} "
              f"draws/plant~{float(r['mean_draws']):.2f}")                          # noqa: float
    print("  -- PC-GRADE (resolution floor) --")
    for mix in (0.0, 0.10, 0.25):                                  # noqa: float
        r = plant_grade(arm, N, R, rng, mix)
        print(f"     mix={mix:<4} mi={r['mi']:+.4f} p={float(r['p']):.4f}")         # noqa: float
    print("  -- PC-PLACEBO (must NOT fire: Sum chi3 is a within-multiset constant) --")
    r = measure(arm, feat_placebo, N, R, rng)
    print(f"     placebo mi={r['mi']:+.6f} p={float(r['p']):.4f} strata={r['s_strata']} "  # noqa: float
          f"(want mi~0, p not <0.01)")

def tier(name, N, R):
    rng = random.Random(SEED)
    sched = load_schedule(); use_random = (name == "ladder")
    print(f"== S5 (r=5 Semaev) tier={name} N={N} R={R} prereg_sha={prereg_sha()[:12]} ==")
    prim = []
    for rec in sched[name]:
        q = rec["q"]; cm = build_cm_arm(rec)
        ncm = build_noncm_arm(q, rec["N"], use_random=use_random)
        rcm = measure(cm, feat_S5, N, R, rng)
        rnc = measure(ncm, feat_S5, N, R, rng)
        rpl = measure(cm, feat_placebo, N, R, rng)
        delta = rcm["mi"] - rnc["mi"]
        prim.append((q, float(rcm["p"]), delta))                   # noqa: float (p display)
        print(f"\n q={q}  CM(B={cm.B},N={cm.N})")
        print(f"  S5-multiset CM: mi={rcm['mi']:+.5f} p={float(rcm['p']):.4f} strata={rcm['s_strata']} "  # noqa: float
              f"N_eff={rcm['N']} | nonCM(N={ncm.N},t={ncm.q+1-ncm.N}): mi={rnc['mi']:+.5f} "              # noqa: float
              f"p={float(rnc['p']):.4f} | Delta={delta:+.5f}")                                            # noqa: float
        print(f"  PC-PLACEBO CM: mi={rpl['mi']:+.6f} p={float(rpl['p']):.4f} (must be within-null)")      # noqa: float
    print("\n  S5-multiset CM p / Delta across primes:")
    for q, p, dl in prim:
        print(f"    q={q}: p={p:.4f} Delta={dl:+.5f}")                          # noqa: float

# ============================ selftest =======================================
def selftest():
    print("== S5 KAT ==")
    q, A, B = 1009, 4, 7
    E = M.Curve(q, A, B); G = M.find_point(E); rng = random.Random(11)
    hits = trials = 0; acc = G
    for _ in range(80):
        acc = E.add(acc, G)
        P = [E.mul(rng.randrange(2, q), G) for _ in range(4)]
        if None in P:
            continue
        s = None
        for pt in P:
            s = E.add(s, pt)
        P5 = E.neg(s)
        if P5 is None:
            continue
        pts5 = P + [P5]
        if any(pt is None for pt in pts5):
            continue
        trials += 1
        if semaev_s5([pt[0] for pt in pts5], A, B, q) == 0:
            hits += 1
    znr = ntot = 0
    for _ in range(300):
        P = [E.mul(rng.randrange(2, q), G) for _ in range(5)]
        if any(pt is None for pt in P):
            continue
        xs = [pt[0] for pt in P]
        if len(set(xs)) < 5:
            continue
        ntot += 1
        if semaev_s5(xs, A, B, q) == 0:
            znr += 1
    print(f"  S5: {hits}/{trials} true 5-relations vanish; {znr}/{ntot} random distinct-x vanish")
    assert hits == trials, "S5 failed on a true 5-relation"
    assert znr < ntot // 10, "S5 vanishes too often on random tuples"
    print("  [ok] S5 vanishes exactly on 5-relations, generic-nonzero otherwise")
    print("  NOTE: coincident-x does NOT force S5=0 for odd r=5 (verified ~random rate); the guard is")
    print("        construction hygiene (x4=x5 zeros S3's lead coeff), not trivial-zero removal.")
    print("== selftest passed ==")

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--tier", choices=["discovery", "confirmation", "ladder"])
    ap.add_argument("--N", type=int, default=0)
    ap.add_argument("--R", type=int, default=1500)
    a = ap.parse_args()
    if a.selftest:
        selftest()
    elif a.controls:
        controls(a.N or 5000, a.R)
    elif a.tier:
        default_N = {"discovery": 5000, "confirmation": 20000, "ladder": 5000}[a.tier]
        tier(a.tier, a.N or default_N, a.R)
    else:
        print(__doc__)
