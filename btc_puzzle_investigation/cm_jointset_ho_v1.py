"""
cm_jointset_ho_v1.py -- runner for PREREG_cm_jointset_higherorder_v1.md (A-joint-HO).

Extends cm_jointset_excess_v3.py to the six channels v3's RESULT named "not settled":
  P1  S4     r=4 Semaev:  Psi4 = chi3(S4(x1..x4)),  J=(sum d) mod 3, cond Phi^pt(4)   [CM vs nonCM]
  P2  C4     m=4 combo:   L_sum over 6 pairs mod 3,  J,               cond Phi^pt(4)   [CM vs nonCM]
  P3  GLV    m=3 mixed:   G = sum chi3(x([lam]Pi+[lam^2]Pj)) mod 3,   cond Phi^pt(3)   [CM-only: (beta x,y)
             is off any non-CM curve, so no matched non-CM feature -> within-null control]
  P4  mu2    ell=2:       Psi2 = chi2(S3),  J2=(sum d) mod 2,         cond Phi2^pt(3)  [CM vs nonCM]
  S-INT      finer intvl: Psi=chi3(S3), J'_k=(sum pos_k) mod 2^k,     cond Phi^pt(3)   [own ledger]
  S-XY       coord pair:  M=(L_sum mod3, Ly_sum mod2), cond full (chi3 x, chi2 y)^3    [own ledger, frontier]
  S-C5       m=5 combo:   L_sum over 10 pairs mod 3, J,               cond Phi^pt(5)   [own ledger, frontier]

SIGNAL PATH exact int/GF(q): curve arithmetic, x/y, chi3, chi2, S3, S4 (resultant), combos,
labels, permutation COUNTS. Float appears ONLY inside the MI (math.log2), a monotone quantity
RANKED against the exact integer within-stratum permutation count (CLAUDE.md carve-out); verdict
p-values are exact Fractions. `check_no_float.sh` must pass (statistic lines tagged # noqa: float).

S4 is Res_X(S3(x1,x2,X), S3(x3,x4,X)); it vanishes iff the two quadratics share a root x5, i.e.
exists P5 with +-P1+-P2+-P5=O and +-P3+-P4-+P5=O  <=>  +-P1+-P2+-P3+-P4=O (the 4-point relation).
CITATION DISCHARGED (citation-verifier 2026-08-25, vs Semaev 2004 Thm 1 + Kosters-Yeo 2015 Prop 2.1,
both PDFs read + SHA'd): our resultant IS exactly Semaev's S4, ABSOLUTELY IRREDUCIBLE, NO extraneous
factor; the iff is exactly the theorem (char != 2,3). The only hygiene issue is a coincident x-coord
(two disjoint equal pairs force a curve-INDEPENDENT trivial S4=0); handled by the draw_sets/plant
coincident-x guard below (== distinct-scalar in-interval). Grade: [CITED - verified against primary text].

Usage:
  python3 cm_jointset_ho_v1.py --selftest
  python3 cm_jointset_ho_v1.py --controls [--N 5000] [--R 2000]
  python3 cm_jointset_ho_v1.py --tier discovery [--N 5000] [--R 2000]
"""
from __future__ import annotations
import sys, math, random, hashlib, argparse, json, itertools
from fractions import Fraction
from collections import defaultdict, Counter
import model_curve_infra_v1 as M

PREREG = "PREREG_cm_jointset_higherorder_v1.md"
SEED = 20260821

# ============================ S4 (new primitive) =============================
def semaev_s4(x1, x2, x3, x4, A, B, q):
    """Res_X(S3(x1,x2,X), S3(x3,x4,X)) mod q -- vanishes iff +-P1+-P2+-P3+-P4=O."""
    def s3coeffs(u, v):
        a2 = (u - v) ** 2 % q
        a1 = (-2 * (((u + v) * (u * v + A)) + 2 * B)) % q
        a0 = (((u * v - A) ** 2) - 4 * B * (u + v)) % q
        return a2, a1, a0
    a2, a1, a0 = s3coeffs(x1, x2)
    b2, b1, b0 = s3coeffs(x3, x4)
    return ((a2 * b0 - a0 * b2) ** 2 - (a2 * b1 - a1 * b2) * (a1 * b0 - a0 * b1)) % q

# ================================ arms =======================================
class Arm:
    def __init__(self, kind, q, A, B, N, beta=None, lam=None):
        self.kind, self.q, self.A, self.B, self.N = kind, q, A, B, N
        self.curve = M.Curve(q, A, B)
        self.zeta = M.cube_root_units(q)[0]
        self.beta, self.lam = beta, lam
        self.L = max(M._prime_factors(N))
        self.G = self._generator()

    def _generator(self):
        cof = self.N // self.L
        is_qr = bytearray(self.q); roots = {}
        for a in range(self.q):
            r = a * a % self.q
            if r not in roots or a < roots[r]:
                roots[r] = a
            is_qr[r] = 1
        for x in range(self.q):
            v = (x * x % self.q * x + self.A * x + self.B) % self.q
            P = None
            if v == 0:
                P = (x, 0)
            elif is_qr[v]:
                y0 = roots[v]; P = (x, min(y0, self.q - y0))
            if P is None:
                continue
            Q = self.curve.mul(cof, P)
            if Q is not None and self.curve.mul(self.L, Q) is None:
                return Q
        raise RuntimeError(f"no order-{self.L} generator on {self.kind} q={self.q}")

    def chi3x(self, P):
        return M.chi3(P[0], self.q, self.zeta) if P is not None else 0
    def chi2x(self, P):
        return M.legendre(P[0], self.q) + 1 if P is not None else 0   # {0,1,2} for {-1,0,1}
    def chi2y(self, P):
        return M.legendre(P[1], self.q) + 1 if P is not None else 0

def build_cm_arm(rec):
    return Arm("CM", rec["q"], 0, rec["B"], rec["N"], beta=rec["beta"], lam=rec["lam"])

def build_noncm_arm(q, target_N, use_random=False):
    r = (M.select_jgen_random(q, target_N, exclude_anomalous=True, budget=1500, seed=q)
         if use_random else M.select_jgen(q, target_N=target_N, exclude_anomalous=True))
    if r is None:
        raise RuntimeError(f"no non-CM match at q={q}")
    return Arm("nonCM", q, r.A, r.B, r.N)

# ============================ MI machinery (from v3) =========================
def _rank_stat(strat, feat, targ):
    joint = Counter()
    for u, a, b in zip(strat, feat, targ):
        joint[(u, a, b)] += 1
    s = 0.0                                                        # noqa: float
    for nb in joint.values():
        s += nb * math.log2(nb)                                    # noqa: float
    return s

def _mi_bits(strat, feat, targ, N):
    by_u = defaultdict(list)
    for i, u in enumerate(strat):
        by_u[u].append(i)
    ln2 = math.log(2)                                              # noqa: float
    mi_raw = 0.0; mm_sum = 0                                       # noqa: float
    for u, idxs in by_u.items():
        nu = len(idxs); joint = Counter(); mf = Counter(); mt = Counter()
        for i in idxs:
            joint[(feat[i], targ[i])] += 1; mf[feat[i]] += 1; mt[targ[i]] += 1
        for (a, b), nab in joint.items():
            ratio = Fraction(nab * nu, mf[a] * mt[b])
            mi_raw += nab * math.log2(ratio)                       # noqa: float
        mm_sum += (len(mf) - 1) * (len(mt) - 1)
    return mi_raw / N + mm_sum / (2 * N * ln2)                     # noqa: float

def within_stratum_perm_test(strat, feat, targ, N, R, rng):
    obs = _rank_stat(strat, feat, targ)
    by_u = defaultdict(list)
    for i, u in enumerate(strat):
        by_u[u].append(i)
    feat = list(feat); ge = 0
    for _ in range(R):
        permuted = feat[:]
        for idxs in by_u.values():
            vals = [feat[i] for i in idxs]; rng.shuffle(vals)
            for i, v in zip(idxs, vals):
                permuted[i] = v
        if _rank_stat(strat, permuted, targ) >= obs:
            ge += 1
    return _mi_bits(strat, feat, targ, N), Fraction(ge + 1, R + 1)

# ============================ intervals / sets ===============================
def interval(q):
    b = q.bit_length() - 1 - 2
    return b, 1 << (b - 1), 1 << b

def draw_sets(arm, m, N, rng):
    b, lo, hi = interval(arm.q)
    assert hi < arm.L, f"interval top {hi} >= subgroup order {arm.L}"
    # COINCIDENT-X GUARD (citation-verifier 2026-08-25, Semaev/Kosters-Yeo): a repeated x-coordinate
    # forces the summation polynomial to a curve-INDEPENDENT trivial-relation zero, injecting a forced
    # feature value. Distinct scalars in [2^(b-1),2^b) give distinct x (d_i+d_j < 2^(b+1) < L), so the
    # x-guard == a distinct-scalar guard, enforceable at draw time. Applied identically to both arms.
    out = []
    while len(out) < N:
        d = tuple(rng.randrange(lo, hi) for _ in range(m))
        if len(set(d)) == m:
            out.append(d)
    return out, (b, lo, hi)

def pts(arm, d):
    return [arm.curve.mul(di, arm.G) for di in d]

# ============================ per-channel features ===========================
def feat_S4(arm, d, P):
    xs = [Pi[0] for Pi in P]
    u = 0
    for Pi in P:
        u = u * 3 + arm.chi3x(Pi)                       # Phi^pt(4), 81 strata
    S4 = semaev_s4(xs[0], xs[1], xs[2], xs[3], arm.A, arm.B, arm.q)
    return u, M.chi3(S4, arm.q, arm.zeta), sum(d) % 3

def feat_C4(arm, d, P):
    u = 0
    for Pi in P:
        u = u * 3 + arm.chi3x(Pi)
    Ls = 0
    for i, j in itertools.combinations(range(4), 2):
        Ls += arm.chi3x(arm.curve.add(P[i], P[j]))
    return u, Ls % 3, sum(d) % 3

def feat_GLV(arm, d, P):
    u = 0
    for Pi in P:
        u = u * 3 + arm.chi3x(Pi)                       # Phi^pt(3), 27 strata
    b1, b2 = arm.beta, arm.beta * arm.beta % arm.q
    G = 0
    for i, j in itertools.combinations(range(3), 2):
        lPi = (b1 * P[i][0] % arm.q, P[i][1]); l2Pj = (b2 * P[j][0] % arm.q, P[j][1])
        lPj = (b1 * P[j][0] % arm.q, P[j][1]); l2Pi = (b2 * P[i][0] % arm.q, P[i][1])
        G += arm.chi3x(arm.curve.add(lPi, l2Pj)) + arm.chi3x(arm.curve.add(lPj, l2Pi))
    return u, G % 3, sum(d) % 3

def feat_mu2(arm, d, P):
    xs = [Pi[0] for Pi in P]
    u = 0
    for Pi in P:
        u = u * 3 + arm.chi2x(Pi)                       # Phi2^pt(3) in {0,1,2}^3
    S3 = M.semaev_s3(xs[0], xs[1], xs[2], arm.A, arm.B, arm.q)
    return u, M.legendre(S3, arm.q) + 1, sum(d) % 2      # Psi2 in {0,1,2}, J2 in {0,1}

def feat_int(arm, d, P, k, lo, hi):
    xs = [Pi[0] for Pi in P]
    u = 0
    for Pi in P:
        u = u * 3 + arm.chi3x(Pi)
    S3 = M.semaev_s3(xs[0], xs[1], xs[2], arm.A, arm.B, arm.q)
    span = hi - lo
    Jk = sum(((di - lo) * (1 << k)) // span for di in d) % (1 << k)   # block position label
    return u, M.chi3(S3, arm.q, arm.zeta), Jk

def feat_xy(arm, d, P):
    u = 0
    for Pi in P:
        u = u * 9 + arm.chi3x(Pi) * 3 + arm.chi2y(Pi)   # full (chi3 x, chi2 y)^3, <=216 strata
    Lx = sum(arm.chi3x(arm.curve.add(P[i], P[j])) for i, j in itertools.combinations(range(3), 2)) % 3
    Ly = sum((arm.chi2y(arm.curve.add(P[i], P[j])) % 2) for i, j in itertools.combinations(range(3), 2)) % 2
    return u, Lx * 2 + Ly, sum(d) % 3                    # M in {0..5}

def feat_C5(arm, d, P):
    u = 0
    for Pi in P:
        u = u * 3 + arm.chi3x(Pi)                        # Phi^pt(5), 243 strata
    Ls = sum(arm.chi3x(arm.curve.add(P[i], P[j])) for i, j in itertools.combinations(range(5), 2))
    return u, Ls % 3, sum(d) % 3

# ============================ measure one channel ============================
def measure(arm, m, featfn, N, R, rng, **kw):
    sets, ival = draw_sets(arm, m, N, rng)
    b, lo, hi = ival
    strat = []; feat = []; targ = []
    for d in sets:
        P = pts(arm, d)
        if None in P:                       # a zero point (d hit subgroup order) -- skip rare
            continue
        if featfn is feat_int:
            u, f, t = featfn(arm, d, P, kw["k"], lo, hi)
        else:
            u, f, t = featfn(arm, d, P)
        strat.append(u); feat.append(f); targ.append(t)
    Nn = len(strat)
    mi, p = within_stratum_perm_test(strat, feat, targ, Nn, R, rng)
    return {"mi": mi, "p": p, "s_strata": len(set(strat)), "N": Nn, "b": b}

# ============================ firing plants ==================================
def plant_generic(arm, m, featfn, N, R, rng, rho, match_fn=None, **kw):
    """Mixture plant: fraction rho of sets get their last d resampled until match_fn(feat,targ).
    match_fn defaults to feat==targ; feat_mu2 uses a QR-bit<->J2 coupling (feat in {0,1,2},
    target J2 in {0,1}: naive feat==targ can only ever hit feat in {0,1}, giving a degenerate
    distinct_planted=1 -- the D-fix couples the QR indicator (feat==2) to J2 so both label
    values are exercised). Uses a REAL independent point (no degenerate linear collapse)."""
    if match_fn is None:
        match_fn = (lambda f, t: (1 if f == 2 else 0) == t) if featfn is feat_mu2 else (lambda f, t: f == t)
    sets, ival = draw_sets(arm, m, N, rng)
    b, lo, hi = ival
    strat = []; feat = []; targ = []; planted_feat = []; planted = 0; draws = 0
    for d in sets:
        d = list(d)
        do_plant = rng.random() < rho                                   # noqa: float
        if do_plant:
            planted += 1; hit = None
            for _try in range(120):
                d[-1] = rng.randrange(lo, hi); draws += 1
                if len(set(d)) < m:          # coincident-x guard on the resampled scalar
                    continue
                P = pts(arm, d)
                if None in P:
                    continue
                if featfn is feat_int:
                    u, f, t = featfn(arm, d, P, kw["k"], lo, hi)
                else:
                    u, f, t = featfn(arm, d, P)
                if match_fn(f, t):
                    hit = (u, f, t); break
            if hit is None:
                P = pts(arm, d)
                if None in P:
                    continue
                u, f, t = (featfn(arm, d, P, kw["k"], lo, hi) if featfn is feat_int
                           else featfn(arm, d, P))
                hit = (u, f, t)
            u, f, t = hit; planted_feat.append(f)
        else:
            P = pts(arm, d)
            if None in P:
                continue
            u, f, t = (featfn(arm, d, P, kw["k"], lo, hi) if featfn is feat_int
                       else featfn(arm, d, P))
        strat.append(u); feat.append(f); targ.append(t)
    Nn = len(strat)
    mi, p = within_stratum_perm_test(strat, feat, targ, Nn, R, rng)
    return {"rho": rho, "mi": mi, "p": p, "distinct_planted": len(set(planted_feat)),
            "n_planted": planted, "mean_draws": Fraction(draws, max(planted, 1))}

# ============================ orchestration ==================================
def prereg_sha():
    try:
        return hashlib.sha256(open(PREREG, "rb").read()).hexdigest()
    except FileNotFoundError:
        return "(prereg not found)"

def load_schedule():
    return json.load(open("schedules_v1/schedule_A_joint_v1.json"))

# channel registry: name, m, featfn, has_noncm, kwargs
CHANNELS = [
    ("P1_S4",  4, feat_S4,  True,  {}),
    ("P2_C4",  4, feat_C4,  True,  {}),
    ("P3_GLV", 3, feat_GLV, False, {}),
    ("P4_mu2", 3, feat_mu2, True,  {}),
    ("S_INT",  3, feat_int, False, {"k": 2}),
    ("S_XY",   3, feat_xy,  False, {}),
    ("S_C5",   5, feat_C5,  False, {}),
]

def holm(pvals, alpha=Fraction(1, 20)):
    """Holm-Bonferroni on a dict name->Fraction p; returns set of rejected names."""
    order = sorted(pvals.items(), key=lambda kv: kv[1])
    m = len(order); rej = set()
    for i, (nm, p) in enumerate(order):
        if p <= alpha / (m - i):        # noqa: float  (exact Fraction division)
            rej.add(nm)
        else:
            break
    return rej

def controls(N, R):
    rng = random.Random(SEED)
    rec = load_schedule()["discovery"][0]
    arm = build_cm_arm(rec)
    print(f"== FIRING CONTROLS (CM q={arm.q} B={arm.B} N={arm.N}) N={N} R={R} ==")
    for name, m, featfn, _, kw in CHANNELS:
        print(f"  -- {name} plant ladder (must fire at rho=0.30) --")
        for rho in (0.0, 0.15, 0.30, 0.60):                            # noqa: float
            r = plant_generic(arm, m, featfn, N, R, rng, rho, **kw)
            print(f"     rho={rho:<4} mi={r['mi']:+.4f} p={float(r['p']):.4f} "  # noqa: float
                  f"distinct_planted={r['distinct_planted']} draws/plant~{float(r['mean_draws']):.2f}")  # noqa: float

def tier(name, N, R):
    rng = random.Random(SEED)
    sched = load_schedule()
    use_random = (name == "ladder")
    print(f"== A-joint-HO tier={name} N={N} R={R} prereg_sha={prereg_sha()[:12]} ==")
    prim_p = defaultdict(list)     # channel -> list of CM p across primes (for reporting)
    for rec in sched[name]:
        q = rec["q"]; cm = build_cm_arm(rec)
        ncm = None
        print(f"\n q={q}  CM(B={cm.B},N={cm.N})")
        for cname, m, featfn, has_ncm, kw in CHANNELS:
            rcm = measure(cm, m, featfn, N, R, rng, **kw)
            line = (f"  {cname:7} CM: mi={rcm['mi']:+.5f} p={float(rcm['p']):.4f} "  # noqa: float
                    f"strata={rcm['s_strata']} N={rcm['N']}")
            if has_ncm:
                if ncm is None:
                    ncm = build_noncm_arm(q, rec["N"], use_random=use_random)
                rnc = measure(ncm, m, featfn, N, R, rng, **kw)
                delta = rcm["mi"] - rnc["mi"]
                line += (f" | nonCM(N={ncm.N},t={ncm.q+1-ncm.N}): mi={rnc['mi']:+.5f} "  # noqa: float
                         f"p={float(rnc['p']):.4f} | Delta={delta:+.5f}")               # noqa: float
            else:
                line += " | [CM-only channel: within-null control]"
            print(line)
            prim_p[cname].append(float(rcm["p"]))                       # noqa: float
    print("\n  per-channel CM p across primes:")
    for cname, _, _, _, _ in CHANNELS:
        ps = prim_p[cname]
        print(f"    {cname:7}: {[round(x,4) for x in ps]}")            # noqa: float

# ============================ selftest =======================================
def selftest():
    print("== S4 KAT ==")
    q, A, B = 1009, 4, 7
    E = M.Curve(q, A, B); G = M.find_point(E)
    hits = trials = 0
    acc = G
    for _ in range(60):
        acc = E.add(acc, G)
        P1 = acc; P2 = E.add(P1, G); P3 = E.add(P2, G)
        if None in (P1, P2, P3):
            continue
        P4 = E.neg(E.add(E.add(P1, P2), P3))     # P4 = -(P1+P2+P3) => 4-relation
        if P4 is None:
            continue
        trials += 1
        if semaev_s4(P1[0], P2[0], P3[0], P4[0], A, B, q) == 0:
            hits += 1
    rng = random.Random(7); zero_neg = 0
    for _ in range(400):
        xs = [rng.randrange(q) for _ in range(4)]
        if semaev_s4(xs[0], xs[1], xs[2], xs[3], A, B, q) == 0:
            zero_neg += 1
    print(f"  S4: {hits}/{trials} true 4-relations vanish; {zero_neg}/400 random 4-tuples vanish")
    assert hits == trials, "S4 failed to vanish on a true 4-relation"
    assert zero_neg < 40, "S4 vanishes too often on random tuples (extraneous factor?)"
    print("  [ok] S4 vanishes exactly on 4-relations, generic-nonzero otherwise")
    # GLV feature sanity: (beta x, y) is on the CM curve; endomorphism check
    rec = load_schedule()["discovery"][0]; arm = build_cm_arm(rec)
    Gx, Gy = arm.G
    assert arm.curve.is_on((arm.beta * Gx % arm.q, Gy)), "(beta x, y) off CM curve"
    print(f"  [ok] GLV endomorphism (beta x,y) on curve; beta={arm.beta} on q={arm.q}")
    print("== selftest passed ==")

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--tier", choices=["discovery", "confirmation", "ladder"])
    ap.add_argument("--N", type=int, default=0)
    ap.add_argument("--R", type=int, default=2000)
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
