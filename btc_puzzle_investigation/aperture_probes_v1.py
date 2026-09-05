#!/usr/bin/env python3
"""aperture_probes_v1.py -- Probe E (interval inversion) + Probe F (twisted incomplete sum).

PREREG: PREREG_aperture_probes_v1.md (frozen before data).

PROBE E -- interval-restricted inversion autocorrelation
    S_E(I) = sum_{j<W} chi_k(w_[d0+j]G) * chi_k(w_[(d0+j)^{-1}]G)
    k in {128,160}, w in {x,y}, I = [d0, d0+W) dyadic.  Null = within-interval value permutation.

PROBE F -- additive-twist incomplete sum (V(a,I) over dyadic intervals)
    V(a,I) = sum_{j<W} chi2(y_[d0+j]G) * e_n(a*(d0+j))
    k=128, K=200 random twist params a.  Statistic = max_{I,a} |V(a,I)|.
    Null = iid +-1 of length W, same twist params.

DISCIPLINE:
    Exact-int signal path (chi2 via Euler criterion, no float on the data).
    Float ONLY inside the monotone statistic (|V(a,I)| for Probe F), ranked vs null.
    check_no_float.py must pass.  Firing controls (C-PLANT, C-NULLSD, C-FIX, C-DUP) mandatory.

BUILDS ON:
    pointwise_inversion_2p128_item5_v1.py (Jacobian arithmetic + batch_x)
    incomplete_sum_2p128_firstorder_v1.py (interval enumeration)

Usage:  python3 aperture_probes_v1.py
"""
import sys, time, math                                  # noqa: float  (math for gcd, cos, sin, sqrt in monotone statistic only)
import numpy as np                                     # noqa: float  (numpy in monotone statistic only)
from random import Random
from gmpy2 import powmod, invert, mpz

# ============================================================================
# secp256k1 parameters
# ============================================================================
P = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F)
N = mpz(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
GX = mpz(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)
GY = mpz(0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
LAM = mpz(0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72)
HALF = (P - 1) // 2

# PREREG-frozen constants
R_NULL = 1000
W_INT  = 2000       # interval width
M_INT  = 50         # number of intervals per arm
K_TWIST = 200       # number of twist parameters for Probe F
BANDS_E = (128, 160)
BAND_F  = 128
SEED_DISC = 20260815
FIRE_NUM, FIRE_DEN = 95, 100
HIT_NUM,  HIT_DEN  = 99, 100


def is_fire(rank, R):
    return rank * FIRE_DEN >= FIRE_NUM * R

def is_hit(rank, R):
    return rank * HIT_DEN >= HIT_NUM * R


# ============================================================================
# Jacobian arithmetic (from pointwise_inversion_2p128_item5_v1.py)
# ============================================================================
def jdbl(A):
    X, Y, Z = A
    if Y == 0:
        return (mpz(0), mpz(0), mpz(0))
    S = 4 * X * Y * Y % P
    M_ = 3 * X * X % P
    Xr = (M_ * M_ - 2 * S) % P
    return (Xr, (M_ * (S - Xr) - 8 * Y ** 4) % P, 2 * Y * Z % P)


def jadd(A, B):
    X1, Y1, Z1 = A
    X2, Y2, Z2 = B
    if Z1 == 0: return B
    if Z2 == 0: return A
    Z1Z1 = Z1 * Z1 % P
    Z2Z2 = Z2 * Z2 % P
    U1 = X1 * Z2Z2 % P
    U2 = X2 * Z1Z1 % P
    S1 = Y1 * Z2 * Z2Z2 % P
    S2 = Y2 * Z1 * Z1Z1 % P
    if U1 == U2:
        return jdbl(A) if S1 == S2 else (mpz(0), mpz(0), mpz(0))
    H = (U2 - U1) % P
    R_ = (S2 - S1) % P
    H2 = H * H % P
    H3 = H2 * H % P
    U1H2 = U1 * H2 % P
    X3 = (R_ * R_ - H3 - 2 * U1H2) % P
    return (X3, (R_ * (U1H2 - X3) - S1 * H3) % P, Z1 * Z2 * H % P)


def jmul(k):
    R_ = (mpz(0), mpz(0), mpz(0))
    Q = (GX, GY, mpz(1))
    while k:
        if k & 1:
            R_ = jadd(R_, Q)
        Q = jdbl(Q)
        k >>= 1
    return R_


def legendre(a):
    a = a % P
    if a == 0: return 0
    return 1 if powmod(a, HALF, P) == 1 else -1


def chi2_x_jac(pt):
    """chi2(x_P) from Jacobian coords: chi2(X) since chi2(Z^2)=1."""
    return legendre(pt[0])


def chi2_y_jac(pt):
    """chi2(y_P) from Jacobian coords: chi2(Y)*chi2(Z) since chi2(Z^3)=chi2(Z)."""
    return legendre(pt[1]) * legendre(pt[2])


def compute_interval_chars(d0, W, char_fn):
    """Compute char_fn([d0+j]G) for j in 0..W-1.  Steps by adding G each time."""
    chars = []
    pt = jmul(d0 % N)
    Gjac = (GX, GY, mpz(1))
    for j in range(W):
        chars.append(char_fn(pt))
        pt = jadd(pt, Gjac)
    return chars


def compute_inverse_chars(ds, char_fn):
    """Compute char_fn([d^{-1}]G) for each d in ds, using batch."""
    inv_pts = [jmul(int(invert(mpz(d), N))) for d in ds]
    return [char_fn(pt) for pt in inv_pts]


# ============================================================================
# Probe E -- interval-restricted inversion autocorrelation
# ============================================================================
def probe_E_arm(k, char_fn, char_label, seed):
    """Run Probe E for one band k and one character."""
    rng = Random(seed)
    nprng = np.random.default_rng(seed)
    t_arm = time.time()
    # sample M_INT interval starts in [2^{k-1}, 2^k)
    d0s = [rng.randrange(2**(k-1), 2**k - W_INT) for _ in range(M_INT)]

    obs_S = []
    all_a = []
    all_b = []
    for d0 in d0s:
        ds = [d0 + j for j in range(W_INT)]
        a_vals = compute_interval_chars(d0, W_INT, char_fn)
        b_vals = compute_inverse_chars(ds, char_fn)
        all_a.append(a_vals)
        all_b.append(b_vals)
        S = sum(a * b for a, b in zip(a_vals, b_vals))
        obs_S.append(S)

    max_obs = max(abs(s) for s in obs_S)

    # null (VECTORIZED): for each of R_NULL draws, permute each interval's b,
    # compute S per interval, take max over intervals.
    # Stack into numpy arrays: a_mat is (M_INT, W), b_mat is (M_INT, W)
    a_mat = np.array(all_a, dtype=np.int64)                     # noqa: float
    b_mat = np.array(all_b, dtype=np.int64)                     # noqa: float
    null_maxes = np.empty(R_NULL, dtype=np.int64)               # noqa: float
    for r in range(R_NULL):
        # permute each row of b_mat independently
        perms = np.array([nprng.permutation(W_INT) for _ in range(M_INT)])  # noqa: float
        b_perm = np.take_along_axis(b_mat, perms, axis=1)
        S_null = np.sum(a_mat * b_perm, axis=1)                  # (M_INT,)
        null_maxes[r] = np.max(np.abs(S_null))

    rank = int(np.sum(null_maxes < max_obs))
    null_sd_emp = int(np.std(null_maxes))                       # noqa: float

    print("  E k=%d %s: max|S|=%-7d  rank %d/%d (%d%%)%s  C-NULLSD emp_max_sd=%d (theory sqrt(W)=%d)  [%.0fs]" %
          (k, char_label, max_obs, rank, R_NULL, rank * 100 // R_NULL,
           " <<<" if is_hit(rank, R_NULL) else (" *" if is_fire(rank, R_NULL) else ""),
           null_sd_emp, int(math.sqrt(W_INT)), time.time() - t_arm), flush=True)   # noqa: float
    return dict(k=k, char=char_label, max_obs=max_obs, rank=rank, obs_S=obs_S)


def probe_E_plant(k, char_fn, char_label, seed, frac_pct):
    """C-PLANT: plant frac_pct% coherent inversion signal; must FIRE."""
    rng = Random(seed + 999)
    nprng = np.random.default_rng(seed + 999)
    d0 = rng.randrange(2**(k-1), 2**k - W_INT)
    ds = [d0 + j for j in range(W_INT)]
    a_vals = np.array(compute_interval_chars(d0, W_INT, char_fn), dtype=np.int64)  # noqa: float
    b_vals = np.array(compute_inverse_chars(ds, char_fn), dtype=np.int64)          # noqa: float
    b_orig = b_vals.copy()
    # plant: force a fraction of b to match a
    n_force = W_INT * frac_pct // 100
    idxs = np.arange(W_INT)                                                        # noqa: float
    nprng.shuffle(idxs)
    b_vals[idxs[:n_force]] = a_vals[idxs[:n_force]]
    S = int(np.sum(a_vals * b_vals))
    # null: permute the ORIGINAL b (unplanted)
    null_vals = np.empty(R_NULL, dtype=np.int64)                                   # noqa: float
    for r in range(R_NULL):
        bb = b_orig.copy()
        nprng.shuffle(bb)
        null_vals[r] = abs(int(np.sum(a_vals * bb)))
    rank = int(np.sum(null_vals < abs(S)))
    print("    C-PLANT(%d%%): |S|=%-7d rank %d/%d (%d%%)  [%s]" %
          (frac_pct, abs(S), rank, R_NULL, rank * 100 // R_NULL,
           "FIRE" if is_fire(rank, R_NULL) else "fail"), flush=True)
    return rank


# ============================================================================
# Probe F -- additive-twist incomplete sum
# ============================================================================
def probe_F_arm(k, seed):
    """Run Probe F: V(a,I) = sum_{d in I} chi2(y_[d]G) * e_n(a*d), max over I and a."""
    rng = Random(seed)
    nprng = np.random.default_rng(seed)
    t_arm = time.time()
    d0s = [rng.randrange(2**(k-1), 2**k - W_INT) for _ in range(M_INT)]
    # sample K_TWIST twist parameters
    twist_as = [rng.randrange(1, int(N)) for _ in range(K_TWIST)]

    # Precompute: for each interval, the character array c (length W) and the
    # phase matrix phases (W x K_TWIST), then V = |c @ phases| for each twist.
    # Precompute phases ONCE (they don't change under the null).
    max_obs = 0
    max_info = None
    all_c_mats = []   # (M_INT,) of (W,) arrays
    all_phase_mats = []  # (M_INT,) of (W, K_TWIST) complex arrays
    for d0 in d0s:
        c_vals = compute_interval_chars(d0, W_INT, chi2_y_jac)
        c_arr = np.array(c_vals, dtype=np.float64)                     # noqa: float
        ds = np.arange(d0, d0 + W_INT, dtype=object)                   # noqa: float
        # phases[j, ai] = exp(2*pi*i * twist_as[ai] * ds[j] / n)
        # compute as: for each twist a, ad mod n, then /n, then exp
        phase_mat = np.empty((W_INT, K_TWIST), dtype=np.complex128)    # noqa: float
        for ai, a in enumerate(twist_as):
            ad_mod = np.array([int(a * int(d) % int(N)) for d in ds], dtype=np.float64)  # noqa: float
            phase_mat[:, ai] = np.exp(2j * np.pi * ad_mod / float(N))  # noqa: float
        all_c_mats.append(c_arr)
        all_phase_mats.append(phase_mat)
        # observed: V[ai] = |sum_j c[j] * phase_mat[j, ai]|
        Vs = np.abs(c_arr @ phase_mat)                                 # noqa: float
        ai_max = int(np.argmax(Vs))
        if Vs[ai_max] > max_obs:
            max_obs = Vs[ai_max]                                      # noqa: float
            max_info = (d0, twist_as[ai_max])

    # null (VECTORIZED): for each draw, random +-1 of length W per interval,
    # compute V = |cnull @ phase_mat| for all twists, take max over (interval, twist).
    null_maxes = np.empty(R_NULL, dtype=np.float64)                    # noqa: float
    for r in range(R_NULL):
        null_max = 0
        for i in range(M_INT):
            cnull = nprng.choice([-1.0, 1.0], size=W_INT)              # noqa: float
            Vs = np.abs(cnull @ all_phase_mats[i])                     # noqa: float
            nm = np.max(Vs)                                           # noqa: float
            if nm > null_max:
                null_max = nm
        null_maxes[r] = null_max

    rank = int(np.sum(null_maxes < max_obs))
    print("  F k=%d: max|V(a,I)|=%-10.1f  rank %d/%d (%d%%)%s  [at d0=%d, a=%d]  [%.0fs]" %
          (k, max_obs, rank, R_NULL, rank * 100 // R_NULL,
           " <<<" if is_hit(rank, R_NULL) else (" *" if is_fire(rank, R_NULL) else ""),
           max_info[0] if max_info else -1, max_info[1] if max_info else -1,
           time.time() - t_arm), flush=True)                            # noqa: float
    return dict(k=k, max_obs=max_obs, rank=rank)


def probe_F_plant(k, seed, frac_pct):
    """C-PLANT for Probe F: plant a single-frequency signal at a known a0."""
    rng = Random(seed + 777)
    nprng = np.random.default_rng(seed + 777)
    d0 = rng.randrange(2**(k-1), 2**k - W_INT)
    a0 = rng.randrange(1, int(N))
    # plant: c(d) = sign(cos(2*pi*a0*d/n)) for frac_pct% of the interval, random otherwise
    c_vals = compute_interval_chars(d0, W_INT, chi2_y_jac)
    planted = list(c_vals)
    n_force = W_INT * frac_pct // 100
    idxs = list(range(W_INT))
    rng.shuffle(idxs)
    for idx in idxs[:n_force]:
        phase = math.cos(2 * math.pi * int(a0 * (d0 + idx) % int(N)) / float(N))   # noqa: float
        planted[idx] = 1 if phase >= 0 else -1
    # compute V(a0, I) on planted
    ds_arr = np.array([d0 + j for j in range(W_INT)], dtype=np.float64)             # noqa: float
    phases = np.exp(2j * np.pi * a0 * ds_arr / float(N))                            # noqa: float
    V_plant = abs(np.sum(np.array(planted, dtype=np.float64) * phases))             # noqa: float
    # null: random +-1
    null_maxes = []
    for _ in range(R_NULL):
        cnull = nprng.choice([-1.0, 1.0], size=W_INT)                               # noqa: float
        V = abs(np.sum(cnull * phases))
        null_maxes.append(V)
    rank = sum(1 for nm in null_maxes if nm < V_plant)
    print("    C-PLANT(%d%%): |V(a0,I)|=%-10.1f rank %d/%d (%d%%)  [%s]" %
          (frac_pct, V_plant, rank, R_NULL, rank * 100 // R_NULL,
           "FIRE" if is_fire(rank, R_NULL) else "fail"))
    return rank


# ============================================================================
# main
# ============================================================================
def main():
    t0 = time.time()
    print("=" * 92)
    print("aperture_probes_v1  --  Probe E (interval inversion) + Probe F (twisted incomplete sum)")
    print("PREREG: PREREG_aperture_probes_v1.md  |  W=%d M=%d K=%d R=%d  SEED=%d" %
          (W_INT, M_INT, K_TWIST, R_NULL, SEED_DISC))
    print("=" * 92)

    print("\n=== Probe E (interval-restricted inversion autocorrelation) ===")
    print("-- discovery seed %d --" % SEED_DISC)
    E_results = []
    for k in BANDS_E:
        for char_fn, char_label in ((chi2_x_jac, "chi2(x)"), (chi2_y_jac, "chi2(y)")):
            res = probe_E_arm(k, char_fn, char_label, SEED_DISC + k)
            E_results.append(res)

    print("\n-- Probe E controls --")
    probe_E_plant(128, chi2_x_jac, "chi2(x)", SEED_DISC, 5)
    probe_E_plant(128, chi2_x_jac, "chi2(x)", SEED_DISC, 2)

    print("\n=== Probe F (additive-twist incomplete sum) ===")
    print("-- discovery seed %d --" % SEED_DISC)
    F_result = probe_F_arm(BAND_F, SEED_DISC)

    print("\n-- Probe F controls --")
    probe_F_plant(BAND_F, SEED_DISC, 5)
    probe_F_plant(BAND_F, SEED_DISC, 2)

    # summary
    print("\n" + "=" * 92)
    print("SUMMARY (discovery seed)")
    print("=" * 92)
    print("Probe E:")
    for r in E_results:
        mk = " <<<" if is_hit(r["rank"], R_NULL) else (" *" if is_fire(r["rank"], R_NULL) else "")
        print("  k=%d %s: rank %d/%d (%d%%)%s" % (r["k"], r["char"], r["rank"], R_NULL, r["rank"]*100//R_NULL, mk))
    print("Probe F:")
    mk = " <<<" if is_hit(F_result["rank"], R_NULL) else (" *" if is_fire(F_result["rank"], R_NULL) else "")
    print("  k=%d: rank %d/%d (%d%%)%s" % (F_result["k"], F_result["rank"], R_NULL, F_result["rank"]*100//R_NULL, mk))

    print("\n[%ds]" % (time.time() - t0))


if __name__ == "__main__":
    main()
