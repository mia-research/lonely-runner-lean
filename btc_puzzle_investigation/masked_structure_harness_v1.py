#!/usr/bin/env python3
"""
masked_structure_harness_v1.py  —  the F / A / D / G cluster.

Tests the "masked structure" idea (additive scalar structure hiding from
multiplicative/geometric readouts of x([d]G)) at the four places our own framework
says it could live.  Everything in the SIGNAL PATH is exact (int / Fraction);
float appears ONLY as a display z-score ranked against a matched permutation null
(per btc_puzzle_investigation/CLAUDE.md).

  F  Isotypic census + the exact anchor:  over any x->-x-closed lift set the cubic
     moment  Sum z^3  is EXACTLY (0,0)  (central symmetry mu_2 in mu_6; z^3 is odd).
     => the full field, the mu_3-CORE, and the FLAP each give Sum z^3 = 0 exactly.
     So E[z^3] is a pure symmetry-BREAKING detector, and the ONLY thing that makes
     it nonzero on a curve set is the QR-restriction of x-coords (curve x != field x).

  A  Cubic moment E[z^3] of the lift, on random FIELD elements (->0), random CURVE
     points (-> the curve baseline mu), a generator ORBIT, and the 82 keys as a SET.
     Matched null = random N-curve-point subsets; control row = a held-out random
     subset must sit in the null bulk.

  D  Frame operator ORIENTATION vs the Frobenius angle.  C_flap principal axis
     (exact, tan(2phi)=sqrt3 * rational) vs the reduced-basis directions R1,R2
     (whose angle is theta=arg(pi_p)).  Int.1 fixed the magnitude (1/2, 3/4); this
     is the untested orientation d.o.f.

  G  The closure-BLIND corner: a multiplicative character chi_k(x([d]G)) has Wiener
     norm ~sqrt(p), so the closure theorem does NOT bound it.  Test whether it leaks
     the additive scalar residue d mod k.  Power-scaling MI on orbit + random-d;
     single-shot on the 82.  Controls: self-MI fires; permutation null is the neg ctrl.

Datasets: random field elements, a generator orbit {x([i]G)}, the 82 solved keys.
"""
import os, csv, math, random
from fractions import Fraction
import numpy as np

from int1_frame_operator_v1 import build, build_secp
from ecc_secp256k1 import scalar_mul, N_ORDER, Gx, Gy, P as SECP_P, _add
from angular_interference_scaling_v1 import conditional, mi_bits, gen_keys, loglog_slope
from lift_sextant_rhombus_law_proof_v2 import reduced_basis

HERE = os.path.dirname(os.path.abspath(__file__))

# ------------------------------------------------------------------ exact ring
# z = u + v*omega,  omega^2 = -1 - omega.
def emul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)
def ecube(z):
    return emul(emul(z, z), z)
def enorm(z):                       # exact N(a+b*omega) = a^2 - a b + b^2
    a, b = z; return a * a - a * b + b * b
def enorm_frac(a, b):               # same, for Fraction components
    return a * a - a * b + b * b

def _pfac(k):
    return {2: {2}, 3: {3}, 6: {2, 3}}[k]
def make_chik(p, k):
    """Exact k-th power residue character F_p* -> {0..k-1} (label of chi in mu_k)."""
    assert (p - 1) % k == 0
    e = (p - 1) // k
    zeta = None; x = 2
    while zeta is None:
        r = pow(x, e, p)
        if r != 1 and all(pow(r, k // q, p) != 1 for q in _pfac(k)):
            zeta = r
        x += 1
    tbl = {}; cur = 1
    for j in range(k):
        tbl[cur] = j; cur = (cur * zeta) % p
    def chik(v):
        v %= p
        return None if v == 0 else tbl[pow(v, e, p)]
    return chik

# ------------------------------------------------------------------ curve helpers
def orbit_x(M):
    """x-coordinate of i*G for i=1..M, incremental (one add/step)."""
    G = (Gx, Gy, 1); acc = (0, 1, 0); out = []
    for _ in range(M):
        acc = _add(acc, G)
        X, Y, Z = acc
        zi = pow(Z, SECP_P - 2, SECP_P)
        out.append((X * zi * zi) % SECP_P)
    return out

def load_82():
    d = []; x = []
    with open(os.path.join(HERE, "puzzles_verified.csv")) as f:
        for r in csv.DictReader(f):
            try:
                dd = int(r["private_key"], 16); xx = int(r["X"], 16)   # private_key is HEX
            except (ValueError, KeyError):
                continue
            d.append(dd); x.append(xx)
    return d, x

# =====================================================================  F
def section_F(p, eis, eps):
    print("\n" + "=" * 74)
    print(f"[F] Isotypic census + exact cubic-moment anchor   (full field p={p})")
    print("=" * 74)
    Sall = [0, 0]; Score = [0, 0]; Sflap = [0, 0]; ncore = nflap = nother = 0
    for x in range(1, p):
        w = eis(x); e = eps(x)
        a, b = ecube(w)
        Sall[0] += a; Sall[1] += b
        if e == 0:
            Score[0] += a; Score[1] += b; ncore += 1
        else:
            Sflap[0] += a; Sflap[1] += b; nflap += 1
            if e == 2: nother += 1
    print(f"  |core|={ncore}  |flap|={nflap}  (flap frac {nflap/(p-1):.4f}; eps==2 'other'={nother})")  # noqa: float
    print(f"  Sum z^3  ALL   = {tuple(Sall)}   (central symmetry x->-x forces (0,0))")
    print(f"  Sum z^3  CORE  = {tuple(Score)}")
    print(f"  Sum z^3  FLAP  = {tuple(Sflap)}")
    ok = (Sall == [0, 0]) and (Score == [0, 0]) and (Sflap == [0, 0])
    print(f"  EXACT anchor  Sum z^3 == 0 on all three sets : {ok}")
    print("  => E[z^3] is a pure symmetry-BREAKING detector.  On a *curve* set the")
    print("     x-coords are QR-restricted (x^3+7 in QR), which breaks x->-x, so the")
    print("     curve baseline E[z^3] can be nonzero.  Census of low mu_6 observables:")
    print("     mass=1 (read), N(z)=norm-band/eps (read), 6-sextant=chi6 covariant (read),")
    print("     z^3 = mu_3-invariant CUBIC  -> the unread component (this is A).")
    return ok

# =====================================================================  A
def cubic_sum(xs, eis):
    Sa = Sb = 0
    for x in xs:
        a, b = ecube(eis(x)); Sa += a; Sb += b
    return Sa, Sb

def mean_cube(xs, eis):
    Sa, Sb = cubic_sum(xs, eis); M = len(xs)
    return Fraction(Sa, M), Fraction(Sb, M)

def section_A(eis_secp, tag_secp, N_POOL=9000, N_ORBIT=40000, B=400, seed=17):
    print("\n" + "=" * 74)
    print(f"[A] mu_3-invariant cubic moment E[z^3]   (curve = {tag_secp})")
    print("=" * 74)
    rng = random.Random(seed)
    print("  (F proved Sum z^3 = 0 EXACTLY over the field/core/flap; the finite-M")
    print("   cubic scale is ~p^1.5/sqrt(M), so the verdict is the matched-null RANK,")
    print("   not an absolute magnitude.  Rank pct in [0.025,0.975] = consistent w/ null.)")

    # pool of random CURVE points (matched-null pool) + population baseline mu
    print(f"  building random-curve-point pool (M={N_POOL}) via scalar_mul ...")
    pool = []
    while len(pool) < N_POOL:
        d = rng.randrange(1, N_ORDER); xy = scalar_mul(d)
        if xy: pool.append(xy[0])
    cube = [ecube(eis_secp(x)) for x in pool]          # exact z^3 of the pool
    Ca = sum(c[0] for c in cube); Cb = sum(c[1] for c in cube)
    mua = Fraction(Ca, N_POOL); mub = Fraction(Cb, N_POOL)   # curve-point baseline mu

    def stat_of_cubes(clist):
        n = len(clist)
        Sa = sum(t[0] for t in clist); Sb = sum(t[1] for t in clist)
        da = Fraction(Sa, n) - mua; db = Fraction(Sb, n) - mub
        return float(enorm_frac(da, db))               # noqa: float (ranked statistic)

    def matched(name, xs):
        n = len(xs)
        stat = stat_of_cubes([ecube(eis_secp(x)) for x in xs])
        # bootstrap null: random size-n subsets of the pool (with replacement so n may exceed pool)
        nulls = np.array([stat_of_cubes([cube[i] for i in rng.choices(range(N_POOL), k=n)])
                          for _ in range(B)])
        pct = float((nulls <= stat).mean())            # noqa: float
        flag = "ANOMALY" if (pct < 0.025 or pct > 0.975) else "null"  # noqa: float
        print(f"    {name:24} N={n:5d}  dist^2={stat:.3e}  rank-pct={pct:.3f}  => {flag}")

    print("  matched-null SET test (null = random curve-point subsets, same N):")
    matched("[ctrl] random-82", [pool[i] for i in rng.sample(range(N_POOL), 82)])
    orb = orbit_x(N_ORBIT)
    matched("generator orbit (N=82)", orb[:82])        # fair N vs the 82
    matched("generator orbit (full)", orb)
    d82, x82 = load_82()
    matched("82 solved keys SET", x82)

# =====================================================================  D
def frame_flap_moments(p, eis, eps):
    Suu = Suv = Svv = 0
    for x in range(1, p):
        if eps(x) != 0:
            u, v = eis(x); Suu += u * u; Suv += u * v; Svv += v * v
    return Suu, Suv, Svv

def axis_rational(Suu, Suv, Svv):
    """principal axis of C in real embedding: tan(2phi) = sqrt3 * rho.  rho exact."""
    num = 2 * Suv - Svv          # 2*(Suv - Svv/2)
    den = 2 * Suu - 2 * Suv - Svv  # 2*(Suu - Suv - Svv/2)
    return Fraction(num, den) if den else None

def flap_anisotropy(Suu, Suv, Svv):
    A = Suu - Suv + Fraction(Svv, 4)
    C = Fraction(3 * Svv, 4)
    # eigenvalues (A+C)/2 +- sqrt(((A-C)/2)^2 + 3*Bc^2) with Bc=(Suv-Svv/2)/2*... use direct:
    half = Fraction(A + C, 2)
    rad2 = (Fraction(A - C, 2)) ** 2 + Fraction(3, 4) * Fraction(2 * Suv - Svv, 2) ** 2
    r = math.sqrt(float(rad2))            # noqa: float (display magnitude)
    lam_max = float(half) + r; lam_min = float(half) - r  # noqa: float
    return lam_max, lam_min

def dir_rational_of_vec(vx, vy):
    """tan(2phi)/sqrt3 = rho for the embedded vector (vx - vy/2, sqrt3/2 vy).
    Re=vx-vy/2, Im=sqrt3/2 vy => tan(2phi)/sqrt3 = (2 vx vy - vy^2)/(2 vx^2 - 2 vx vy - vy^2)."""
    num = 2 * vx * vy - vy * vy
    den = 2 * vx * vx - 2 * vx * vy - vy * vy
    return Fraction(num, den) if den else None

def _align(rho, R1, R2):
    """which of R1, R2, or the rhombus diagonals R1+-R2 the principal axis matches."""
    cand = {"R1": R1, "R2": R2,
            "diag(R1+R2)": (R1[0] + R2[0], R1[1] + R2[1]),
            "diag(R1-R2)": (R1[0] - R2[0], R1[1] - R2[1])}
    hits = [nm for nm, v in cand.items() if dir_rational_of_vec(*v) == rho]
    return "+".join(hits) if hits else "neither(exact)"

def section_D(primes_small, p100003, eis100, eps100, eis_secp, eps_secp):
    print("\n" + "=" * 74)
    print("[D] Frame-operator ORIENTATION of C_flap vs the reduced basis (theta)")
    print("=" * 74)
    print("  rho_axis := tan(2phi)/sqrt3 for C_flap's principal axis; compare to")
    print("  rho(R1), rho(R2) of the reduced basis (angle = arg(pi_p) = theta).")

    def one(p, eis, eps, R1, R2):
        Suu, Suv, Svv = frame_flap_moments(p, eis, eps)
        rho = axis_rational(Suu, Suv, Svv)
        lam_max, lam_min = flap_anisotropy(Suu, Suv, Svv)
        aniso = lam_max / lam_min if lam_min > 0 else float('inf')  # noqa: float
        print(f"  p={p:>10}: rho_axis={_fs(rho)}  align:{_align(rho, R1, R2):14}"
              f"  C_flap lam_max/lam_min={aniso:.2f}")

    for p in primes_small:
        eis, eps = build(p); R1, R2 = reduced_basis(p)
        one(p, eis, eps, tuple(R1), tuple(R2))
    R1, R2 = reduced_basis(p100003)
    one(p100003, eis100, eps100, tuple(R1), tuple(R2))
    # secp: full-field enumeration impossible; sample the flap moments
    print("  secp (sampled 200k for the flap moments):")
    rng = random.Random(3)
    Suu = Suv = Svv = 0
    for _ in range(200000):
        x = rng.randrange(1, SECP_P)
        if eps_secp(x) != 0:
            u, v = eis_secp(x); Suu += u * u; Suv += u * v; Svv += v * v
    from eisenstein_lift_sextant_exact_v1 import R1 as R1s, R2 as R2s
    rho = axis_rational(Suu, Suv, Svv)
    lam_max, lam_min = flap_anisotropy(Suu, Suv, Svv)
    # sampled moments -> rho is approximate; report nearest by float distance
    cand = {"R1": tuple(R1s), "R2": tuple(R2s),
            "diag(R1+R2)": (R1s[0] + R2s[0], R1s[1] + R2s[1]),
            "diag(R1-R2)": (R1s[0] - R2s[0], R1s[1] - R2s[1])}
    near = min(cand, key=lambda nm: abs(float(dir_rational_of_vec(*cand[nm])) - float(rho)))  # noqa: float
    print(f"  p=secp(samp): rho_axis~{float(rho):+.6f}  nearest:{near} "  # noqa: float
          f"(rho={float(dir_rational_of_vec(*cand[near])):+.6f})  "  # noqa: float
          f"C_flap lam_max/lam_min={lam_max/lam_min:.2f}")  # noqa: float

def _fs(fr):
    if fr is None: return "inf"
    return f"{float(fr):+.4f}"  # noqa: float

# =====================================================================  G
def section_G(N=40000, seed=23):
    print("\n" + "=" * 74)
    print("[G] Multiplicative readout chi_k(x([d]G)) vs additive scalar residue d mod k")
    print("=" * 74)
    print("  closure-BLIND corner (||chi_k||_A ~ sqrt(p)).  VERDICT = the SCALING trend")
    print("  (signal: Ic plateaus + z grows ~sqrt(M);  noise: Ic~1/M, z does not grow).")
    print("  A single-M z>3 is NOT a signal -- perm-null z fluctuates (audited).")
    chi = {k: make_chik(SECP_P, k) for k in (2, 3, 6)}
    Ms = [m for m in (2000, 5000, 10000, 20000, 40000) if m <= N]
    if len(Ms) < 3:
        print(f"  only {len(Ms)} sample size(s) available at N={N}; verdicts are trend-undetermined.")
    rng = np.random.default_rng(seed)

    def run(name, ds, xs):
        ds = np.array([int(d) for d in ds]); xs = list(xs)
        for k in (2, 3, 6):
            feat = np.array([chi[k](x) if chi[k](x) is not None else 0 for x in xs], dtype=np.int64)
            targ = (ds % k).astype(np.int64)
            res = conditional(feat, targ, Ms, 300, rng)
            Ic = [r[1] for r in res]; z = [r[2] for r in res]
            if len(Ms) >= 3:
                s_mi = loglog_slope(Ms, Ic)                          # ~0 plateau (signal); ~-1 noise
                s_z = float(np.polyfit(np.sqrt(np.array(Ms, float)), np.array(z, float), 1)[0])  # noqa: float
                tag = "SIGNAL" if (s_mi > -0.5 and s_z > 0 and z[-1] > 4) else "null"  # noqa: float
            else:
                s_mi = float("nan")  # noqa: float
                tag = "trend-undetermined"
            self_mi = mi_bits(feat[:Ms[-1]], feat[:Ms[-1]])          # detector-fires control
            print(f"    {name:14} chi_{k} vs d%{k}: Ic {Ic[0]:+.5f}->{Ic[-1]:+.5f} "
                  f"z {z[0]:+.1f}->{z[-1]:+.1f} slope(Ic)={s_mi:+.2f} "
                  f"[selfMI={self_mi:.2f}] => {tag}")

    # generator orbit: d = i
    orb = orbit_x(N)
    run("orbit", list(range(1, N + 1)), orb)
    # random-d curve points
    dR, XR, _ = gen_keys(64, N, seed)
    run("random-d(64b)", dR, XR)
    # the 82 as a SET (single-shot; underpowered)
    d82, x82 = load_82()
    print("  82 solved keys (single-shot MI + permutation p-value; N=82 underpowered):")
    for k in (2, 3, 6):
        feat = np.array([chi[k](x) if chi[k](x) is not None else 0 for x in x82], dtype=np.int64)
        targ = np.array([d % k for d in d82], dtype=np.int64)
        raw = mi_bits(feat, targ)
        nulls = np.array([mi_bits(feat, targ[rng.permutation(len(targ))]) for _ in range(2000)])
        pval = float((nulls >= raw).mean())  # noqa: float
        print(f"    chi_{k}(x[dG]) vs d%{k}:  MI={raw:.4f} bits  perm p={pval:.3f}  "
              f"(self-MI feat={mi_bits(feat, feat):.3f})")

# =====================================================================  main
def main():
    print("MASKED-STRUCTURE HARNESS v1  —  F / A / D / G   (exact signal path)")
    p = 100003
    eis100, eps100 = build(p)
    ok = section_F(p, eis100, eps100)
    eis_secp, eps_secp = build_secp()
    section_A(eis_secp, "secp256k1")
    section_D([103, 1009, 10009], p, eis100, eps100, eis_secp, eps_secp)
    section_G()
    print("\nDONE.")

if __name__ == "__main__":
    main()
