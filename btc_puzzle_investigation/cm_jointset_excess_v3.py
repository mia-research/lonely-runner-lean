"""
cm_jointset_excess_v3.py -- runner for PREREG_cm_jointset_excess_v3.md (A-joint).
v3 vs v2: the omnibus guard is coarsened from the (unestimable at feasible N) 27x27|27
table to the estimable 3x3|27 statistic I(L_sum ; J | Phi^pt), L_sum=(L12+L13+L23) mod 3;
its firing control PC-LIN is replaced by the non-degenerate mixture PC-COMBO.

Imports the staged infra `model_curve_infra_v1.py`. SIGNAL PATH is exact int/GF(q):
curve arithmetic, x-coords, chi3, Semaev S3, labels, and all permutation COUNTS are
integers. Float appears ONLY inside the mutual-information statistic (math.log2), used
as a monotone quantity RANKED against an exact integer within-stratum permutation
count -- the sanctioned carve-out (CLAUDE.md; prereg v2 sec 8). The verdict p-value is
an exact Fraction of integer counts.

Object: the synergy E = I(Psi ; J | Phi^pt), Psi = chi3(S3(x1,x2,x3)), J = (d1+d2+d3) mod 3,
Phi^pt = (chi3(x1),chi3(x2),chi3(x3)). Verdict: Delta = I_prim(CM) - I_prim(nonCM).

Usage:
  python3 cm_jointset_excess_v3.py --controls [--R 2000]      # firing controls only
  python3 cm_jointset_excess_v3.py --tier discovery [--R 10000]
"""
from __future__ import annotations
import sys, math, random, hashlib, argparse, json
from fractions import Fraction
from collections import defaultdict, Counter
import model_curve_infra_v1 as M

PREREG = "PREREG_cm_jointset_excess_v3.md"
SEED = 20260821

# ---------------------------------------------------------------------------
# arms
# ---------------------------------------------------------------------------

class Arm:
    def __init__(self, kind, q, A, B, N):
        self.kind, self.q, self.A, self.B, self.N = kind, q, A, B, N
        self.curve = M.Curve(q, A, B)
        self.zeta = M.cube_root_units(q)[0]           # fixed primitive cube root mod q
        self.L = max(M._prime_factors(N))             # largest prime factor = subgroup order
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
            Q = self.curve.mul(cof, P)                # order divides L (L prime)
            if Q is not None and self.curve.mul(self.L, Q) is None:
                return Q                              # order exactly L
        raise RuntimeError(f"no order-{self.L} generator on {self.kind} q={self.q}")

    def chi3x(self, P):
        return M.chi3(P[0], self.q, self.zeta) if P is not None else 0

def build_cm_arm(rec):    # rec from schedule_A_joint arms(): {q,B,N,...}
    return Arm("CM", rec["q"], 0, rec["B"], rec["N"])

def build_noncm_arm(q, target_N, use_random=False):
    # use_random: bounded random-search matcher (ladder DEVIATION, see v3 DEVIATIONS) where the
    # enumerative select_jgen is intractable (q >= ~2^14 with no early exact match).
    if use_random:
        r = M.select_jgen_random(q, target_N, exclude_anomalous=True, budget=1500, seed=q)
    else:
        r = M.select_jgen(q, target_N=target_N, exclude_anomalous=True)
    if r is None:
        raise RuntimeError(f"no non-CM match at q={q}")
    return Arm("nonCM", q, r.A, r.B, r.N)

# ---------------------------------------------------------------------------
# feature extraction for a set (d1,d2,d3)
# ---------------------------------------------------------------------------

def features(arm, d):
    P = [arm.curve.mul(di, arm.G) for di in d]
    xs = [Pi[0] for Pi in P]
    phi = tuple(arm.chi3x(Pi) for Pi in P)            # in {0,1,2}^3
    u = phi[0] * 9 + phi[1] * 3 + phi[2]              # stratum index 0..26
    S3 = M.semaev_s3(xs[0], xs[1], xs[2], arm.A, arm.B, arm.q)
    psi = M.chi3(S3, arm.q, arm.zeta)                 # chi3(0)=0
    J = (d[0] + d[1] + d[2]) % 3
    return u, psi, J, P, S3

def omnibus_features(arm, d, P):
    """v3 coarsened omnibus: L_sum = (L12+L13+L23) mod 3 vs J = (d1+d2+d3) mod 3,
    L_ij = chi3(x(P_i+P_j)). A 3x3 table (conditioned on Phi^pt, 27 strata) -- estimable
    at feasible N, unlike v2's 27x27|27 (which had every joint cell count <= 1)."""
    def Lij(i, j):
        R = arm.curve.add(P[i], P[j])
        return arm.chi3x(R)                            # chi3(0)=0 if R=O
    L_sum = (Lij(0, 1) + Lij(0, 2) + Lij(1, 2)) % 3
    J = (d[0] + d[1] + d[2]) % 3
    return L_sum, J

# ---------------------------------------------------------------------------
# conditional-MI statistic  I(feat ; targ | stratum)
# ranking core (permutation-varying part only) is integer counts * log2(count)
# reported value is Miller-Madow corrected bits
# ---------------------------------------------------------------------------

def _rank_stat(strat, feat, targ):
    """Permutation-varying part of the conditional MI: sum over (u,a,b) of n*log2(n).
    Monotone with I(feat;targ|stratum) when marginals are held fixed (within-stratum perm)."""
    joint = Counter()
    for u, a, b in zip(strat, feat, targ):
        joint[(u, a, b)] += 1
    s = 0.0   # noqa: float  (MI ranking statistic accumulator)
    for n in joint.values():
        s += n * math.log2(n)
    return s

def _mi_bits(strat, feat, targ, N):
    """Miller-Madow corrected I(feat;targ|stratum) in bits (reported value)."""
    by_u = defaultdict(list)
    for i, u in enumerate(strat):
        by_u[u].append(i)
    ln2 = math.log(2)
    mi_raw = 0.0   # noqa: float  (MI statistic accumulator)
    mm_sum = 0
    for u, idxs in by_u.items():
        nu = len(idxs)
        joint = Counter(); mf = Counter(); mt = Counter()
        for i in idxs:
            joint[(feat[i], targ[i])] += 1; mf[feat[i]] += 1; mt[targ[i]] += 1
        for (a, b), nab in joint.items():
            ratio = Fraction(nab * nu, mf[a] * mt[b])
            mi_raw += nab * math.log2(ratio)
        mm_sum += (len(mf) - 1) * (len(mt) - 1)
    return mi_raw / N + mm_sum / (2 * N * ln2)        # noqa: float  (MI statistic, not signal path)

def within_stratum_perm_test(strat, feat, targ, N, R, rng):
    """Return (mi_bits_obs, exact perm p, mi_bits_null_mean). Permute `feat` within each
    stratum (preserves p(feat|stratum) and the target structure; destroys only the
    within-stratum feat<->targ coupling) -- the exact matched null for conditional MI."""
    obs = _rank_stat(strat, feat, targ)
    by_u = defaultdict(list)
    for i, u in enumerate(strat):
        by_u[u].append(i)
    feat = list(feat)
    ge = 0
    null_sum = 0.0   # noqa: float  (MI null-mean accumulator)
    for _ in range(R):
        permuted = feat[:]
        for idxs in by_u.values():
            vals = [feat[i] for i in idxs]
            rng.shuffle(vals)
            for i, v in zip(idxs, vals):
                permuted[i] = v
        st = _rank_stat(strat, permuted, targ)
        null_sum += st
        if st >= obs:
            ge += 1
    p = Fraction(ge + 1, R + 1)
    return _mi_bits(strat, feat, targ, N), p, null_sum

# ---------------------------------------------------------------------------
# set drawing
# ---------------------------------------------------------------------------

def interval(q):
    b = q.bit_length() - 1 - 2          # floor(log2 q) - 2
    return b, 1 << (b - 1), 1 << b      # b, lo=2^(b-1), hi=2^b

def draw_sets(arm, N, rng):
    b, lo, hi = interval(arm.q)
    assert hi < arm.L, f"interval top {hi} >= subgroup order {arm.L}"
    out = []
    for _ in range(N):
        d = (rng.randrange(lo, hi), rng.randrange(lo, hi), rng.randrange(lo, hi))
        out.append(d)
    return out, (b, lo, hi)

# ---------------------------------------------------------------------------
# firing controls
# ---------------------------------------------------------------------------

def run_pc_sem(arm, N, R, rng, rho):
    """PC-SEM v2 (mixture): planted fraction rho has d3 resampled until
    chi3(S3) == (d1+d2+d3) mod 3, using a REAL curve point (S3 generically nonzero).
    Non-degeneracy guard: Psi non-constant on planted, S3!=0 on >=99% planted."""
    b, lo, hi = interval(arm.q)
    strat = []; psi = []; J = []
    planted_psi = []; s3_zero = 0; draws = 0; planted = 0
    for _ in range(N):
        d1, d2 = rng.randrange(lo, hi), rng.randrange(lo, hi)
        if rng.random() < rho:  # noqa: float  (plant membership coin, not signal path)
            planted += 1
            hit = None
            for _try in range(100):
                d3 = rng.randrange(lo, hi); draws += 1
                u, ps, j, P, S3 = features(arm, (d1, d2, d3))
                if ps == j:
                    hit = (u, ps, j, S3); break
            if hit is None:
                u, ps, j, P, S3 = features(arm, (d1, d2, rng.randrange(lo, hi)))
                hit = (u, ps, j, S3)
            u, ps, j, S3 = hit
            planted_psi.append(ps); s3_zero += (S3 == 0)
        else:
            d3 = rng.randrange(lo, hi)
            u, ps, j, P, S3 = features(arm, (d1, d2, d3))
        strat.append(u); psi.append(ps); J.append(j)
    guard_ok = (len(set(planted_psi)) >= 2) and (s3_zero <= planted // 100)
    mi, p, _ = within_stratum_perm_test(strat, psi, J, N, R, rng)
    return {"rho": rho, "mi": mi, "p": p, "guard_ok": guard_ok,
            "mean_draws": Fraction(draws, max(planted, 1)),
            "n_distinct_planted_psi": len(set(planted_psi)), "s3_zero_planted": s3_zero,
            "n_planted": planted}

def run_pc_grade(arm, N, R, rng, mix):
    """Psi_plant = (J + Uniform3 with prob mix) -- abstract coupled feature, floor calibration."""
    b, lo, hi = interval(arm.q)
    strat = []; psi = []; J = []
    for _ in range(N):
        d = (rng.randrange(lo, hi), rng.randrange(lo, hi), rng.randrange(lo, hi))
        u, ps, j, P, S3 = features(arm, d)
        ps_plant = j if rng.random() < mix else rng.randrange(3)  # noqa: float
        strat.append(u); psi.append(ps_plant); J.append(j)
    mi, p, _ = within_stratum_perm_test(strat, psi, J, N, R, rng)
    return {"mix": mix, "mi": mi, "p": p}

def run_pc_combo(arm, N, R, rng, rho):
    """PC-COMBO v3 (mixture) -- firing control for the coarsened omnibus I(L_sum;J|Phi^pt).
    Planted fraction rho: resample d3 until L_sum == J, using a REAL INDEPENDENT point P3.
    (Note: the naive linear plant d3=-(d1+d2) is degenerate here -- it forces P3=-(P1+P2),
    collapsing every combo x(Pi+Pj) into a per-point coordinate, so L_sum becomes a function
    of Phi^pt and I(L_sum;J|Phi^pt)=0. An independent resampled P3 avoids that collapse.)"""
    b, lo, hi = interval(arm.q)
    strat = []; lsum = []; J = []; planted_ls = []; planted = 0; draws = 0
    for _ in range(N):
        d1, d2 = rng.randrange(lo, hi), rng.randrange(lo, hi)
        if rng.random() < rho:  # noqa: float  (plant membership coin, not signal path)
            planted += 1; hit = None
            for _try in range(100):
                d3 = rng.randrange(lo, hi); draws += 1
                u, ps, j, P, S3 = features(arm, (d1, d2, d3))
                ls, jj = omnibus_features(arm, (d1, d2, d3), P)
                if ls == jj:
                    hit = (u, ls, jj); break
            if hit is None:
                d3 = rng.randrange(lo, hi)
                u, ps, j, P, S3 = features(arm, (d1, d2, d3))
                ls, jj = omnibus_features(arm, (d1, d2, d3), P); hit = (u, ls, jj)
            u, ls, jj = hit; planted_ls.append(ls)
        else:
            d3 = rng.randrange(lo, hi)
            u, ps, j, P, S3 = features(arm, (d1, d2, d3))
            ls, jj = omnibus_features(arm, (d1, d2, d3), P)
        strat.append(u); lsum.append(ls); J.append(jj)
    guard_ok = len(set(planted_ls)) >= 2
    mi, p, _ = within_stratum_perm_test(strat, lsum, J, N, R, rng)
    return {"rho": rho, "mi": mi, "p": p, "guard_ok": guard_ok,
            "n_distinct_planted_lsum": len(set(planted_ls)), "n_planted": planted,
            "mean_draws": Fraction(draws, max(planted, 1))}

# ---------------------------------------------------------------------------
# primary arm measurement
# ---------------------------------------------------------------------------

def measure_arm(arm, N, R, rng):
    sets, ival = draw_sets(arm, N, rng)
    strat = []; psi = []; J = []; Lsum = []; Jp = []
    b, lo, hi = ival; half = lo + (hi - lo) // 2
    for d in sets:
        u, ps, j, P, S3 = features(arm, d)
        ls, jj = omnibus_features(arm, d, P)          # ls=L_sum, jj==j
        jp = sum(1 if di >= half else 0 for di in d) % 2
        strat.append(u); psi.append(ps); J.append(j)
        Lsum.append(ls); Jp.append(jp)
    mi_prim, p_prim, _ = within_stratum_perm_test(strat, psi, J, N, R, rng)
    mi_omni, p_omni, _ = within_stratum_perm_test(strat, Lsum, J, N, R, rng)
    mi_sec, p_sec, _ = within_stratum_perm_test(strat, psi, Jp, N, R, rng)
    s = len(set(strat))
    return {"arm": arm.kind, "q": arm.q, "A": arm.A, "B": arm.B, "N": arm.N,
            "trace": arm.q + 1 - arm.N, "gen_order": arm.L, "interval_b": b,
            "s_strata": s, "mi_prim": mi_prim, "p_prim": p_prim,
            "mi_omni": mi_omni, "p_omni": p_omni, "mi_sec": mi_sec, "p_sec": p_sec}

# ---------------------------------------------------------------------------
# orchestration
# ---------------------------------------------------------------------------

def prereg_sha():
    try:
        return hashlib.sha256(open(PREREG, "rb").read()).hexdigest()
    except FileNotFoundError:
        return "(prereg file not found)"

def load_schedule():
    return json.load(open("schedules_v1/schedule_A_joint_v1.json"))

def controls(N, R):
    rng = random.Random(SEED)
    sched = load_schedule()
    rec = sched["discovery"][0]                       # smallest discovery prime
    arm = build_cm_arm(rec)
    print(f"== FIRING CONTROLS on CM arm q={arm.q} B={arm.B} N={arm.N} (N={N}, R={R}) ==")
    for rho in (0.0, 0.15, 0.30, 0.60):   # noqa: float  (plant-rate schedule, not signal path)
        r = run_pc_sem(arm, N, R, rng, rho)
        print(f"  PC-SEM rho={rho:<4}: mi={r['mi']:+.4f} p={float(r['p']):.4f} "  # noqa: float
              f"guard_ok={r['guard_ok']} distinct_psi={r['n_distinct_planted_psi']} "
              f"s3zero={r['s3_zero_planted']}/{r['n_planted']} draws/plant~{float(r['mean_draws']):.2f}")  # noqa: float
    for mix in (0.0, 0.10, 0.25):   # noqa: float  (plant-mix schedule, not signal path)
        r = run_pc_grade(arm, N, R, rng, mix)
        print(f"  PC-GRADE mix={mix:<4}: mi={r['mi']:+.4f} p={float(r['p']):.4f}")  # noqa: float
    for rho in (0.0, 0.15, 0.30, 0.60):   # noqa: float  (plant-rate schedule, not signal path)
        r = run_pc_combo(arm, N, R, rng, rho)
        print(f"  PC-COMBO rho={rho:<4}: mi={r['mi']:+.4f} p={float(r['p']):.4f} "  # noqa: float
              f"guard_ok={r['guard_ok']} distinct_lsum={r['n_distinct_planted_lsum']} "
              f"draws/plant~{float(r['mean_draws']):.2f}")  # noqa: float

def tier(name, N, R):
    rng = random.Random(SEED)
    sched = load_schedule()
    print(f"== A-joint v3 tier={name} N={N} R={R} prereg_sha={prereg_sha()[:12]} ==")
    rows = []
    use_random = (name == "ladder")   # DEVIATION: random-search non-CM matcher for the ladder only
    for rec in sched[name]:
        q = rec["q"]
        cm = build_cm_arm(rec)
        ncm = build_noncm_arm(q, rec["N"], use_random=use_random)
        rcm = measure_arm(cm, N, R, rng)
        rncm = measure_arm(ncm, N, R, rng)
        delta = rcm["mi_prim"] - rncm["mi_prim"]
        rows.append((q, rcm, rncm, delta))
        print(f"  q={q}: CM I_prim={rcm['mi_prim']:+.4f} (p={float(rcm['p_prim']):.4f}) | "  # noqa: float
              f"nonCM(N={rncm['N']},t={rncm['trace']}) I_prim={rncm['mi_prim']:+.4f} "  # noqa: float
              f"(p={float(rncm['p_prim']):.4f}) | Delta={delta:+.4f}")  # noqa: float
        print(f"        CM channels: omni(combo) mi={rcm['mi_omni']:+.4f} p={float(rcm['p_omni']):.4f} | "  # noqa: float
              f"sec(interval) mi={rcm['mi_sec']:+.4f} p={float(rcm['p_sec']):.4f} | s_strata={rcm['s_strata']}")  # noqa: float
    signs = [1 if d > 0 else 0 for (_, _, _, d) in rows]
    print(f"  Delta>0 on {sum(signs)}/{len(signs)} primes (paired-sign direction)")
    return rows

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--controls", action="store_true")
    ap.add_argument("--tier", choices=["discovery", "confirmation", "ladder"])
    ap.add_argument("--N", type=int, default=0)
    ap.add_argument("--R", type=int, default=10000)
    args = ap.parse_args()
    if args.controls:
        controls(args.N or 5000, args.R)
    elif args.tier:
        default_N = {"discovery": 5000, "confirmation": 20000, "ladder": 5000}[args.tier]
        tier(args.tier, args.N or default_N, args.R)
    else:
        print(__doc__)
