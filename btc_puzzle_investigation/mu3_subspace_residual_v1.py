#!/usr/bin/env python3
"""mu3_subspace_residual_v1.py -- three probes on the mu3-forced subspace residual.

OBJECT (CORRECTION_deflation_overreach_v1.md section 4.2, restored):
  c(d) = chi2(y_{[d]G}) is FORCED into the mu3-invariant subspace: c(m*d) = c(d) for m of order 3
  in (Z/n)*, and c(-d) = eps * c(d).  The n-1 signs carry (n-1)/6 free values on the cyclic quotient
  Q6 = (Z/n)* / mu6,  |Q6| = L = (n-1)/6.  j=0-specific, hence present on secp256k1.

THE THREE PROBES (PREREG_mu3_subspace_residual_v1.md, frozen before data):
  A. Subgroup-restricted partial sums on Q6 (cosets of H_q, small prime q | L).
  B. The d^{-1} involution autocorrelation on Q6  +  the d^k map autocorrelations (non-algebraic
     index channel -- the one wall Weil does not close, STRUCTURAL_IMPLICATIONS section 5.3).
  C. Incomplete-sum concentration at controlled aperture (sliding windows of length w on Q6).

DISCIPLINE (CLAUDE.md):
  - Exact-integer signal path: Legendre, dlog, index arithmetic.  No float in the signal path.
  - Float appears ONLY inside a monotone statistic (transform magnitude / correlation value),
    ranked against a MATCHED permutation null.  The verdict is an integer rank in every cell.
  - Firing control (planted-leak) MUST fire at every prime; random control MUST stay flat.
    If a control fails the instrument is invalid and no verdict is issued for that prime.
  - NO float literals anywhere: plant fractions and rank thresholds are integer ratios.

BUILDS ON (unchanged):
  mu3_forced_subspace_object_v1.build(p)  -- returns the reduced sequence u on Q6 + verifies both
                                            forced symmetries.
  audit_n1_vsign_v2_core                  -- tonelli, legendre, is_prime.
  jclass_e2_relation_probe_v1             -- curve_order_p, dlog_table_p, points_p.

Usage:  python mu3_subspace_residual_v1.py
"""
import random, sys, math                                                 # noqa: float
import audit_n1_vsign_v2_core as core
from jclass_e2_relation_probe_v1 import curve_order_p, dlog_table_p, points_p
from mu3_forced_subspace_object_v1 import build as _mu3_build, primitive_root

# ============================================================================
# PREREG-frozen constants  (integer-only; no float literals)
# ============================================================================
R_NULL = 3000          # permutation-null draws per cell
SEED   = 20260808      # frozen in PREREG section 6
PRIMES_IN = (43, 67, 79, 127, 163, 211, 547)
PRIMES_S  = (823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503)
PRIMES_C  = (577, 733, 1237, 1249, 1669)

# rank thresholds as integer ratios:  rank >= NUM/DEN * R_NULL  <=>  rank*DEN >= NUM*R_NULL
FIRE_NUM, FIRE_DEN = 95, 100      # 0.95
HIT_NUM,  HIT_DEN  = 99, 100      # 0.99

# plant-control fraction f = 0.30 = 3/10  (how many signs to force)
PLANT_NUM, PLANT_DEN = 3, 10

# Probe A parameters: small primes q with 2 <= q <= min(L//2, 200)
PROBE_A_QCAP = 200
# Probe B parameters: admissible odd k, gcd(k,6)=1, 3 <= k <= 25
PROBE_B_KS   = (3, 5, 7, 11, 13, 17, 19, 23, 25)
# Probe C parameters: window lengths
PROBE_C_WS   = (2, 4, 8, 16, 32, 64)


def is_fire(rank):
    """rank >= 0.95 * R_NULL, via integer cross-multiply."""
    return rank * FIRE_DEN >= FIRE_NUM * R_NULL

def is_hit(rank):
    """rank >= 0.99 * R_NULL, via integer cross-multiply."""
    return rank * HIT_DEN >= HIT_NUM * R_NULL


# ============================================================================
# helpers -- exact-integer index arithmetic on (Z/n)* and its quotient Q6
# ============================================================================
def build_q6(p, B=7):
    """Return dict with n, m, eps, g, L, u, reps, d_to_q6idx, c.

    c[d]   = chi2(y_{[d]G}) in {+1,-1}, exact integer, for d in 1..n-1.
    u[j]   = c[reps[j]], the reduced sign sequence on Q6, length L = (n-1)//6.
    reps   = canonical mu6 coset representatives (same rule as run_n1_120deg_v1.mu6_reps).
    d_to_q6idx maps every d in 1..n-1 to its Q6 index j in 0..L-1.
    g      = primitive root mod n (generator of (Z/n)*).
    """
    b = _mu3_build(p, B)
    if b is None:
        return None
    n   = b["n"]
    m   = b["m"]
    eps = b["eps"]
    if not core.is_prime(n) or (n - 1) % 6 != 0:
        return None

    # -- the full sign sequence c(d) for d in 1..n-1 (exact integer)
    dl, cyc = dlog_table_p(p, 0, B, n)
    if not cyc:
        return None
    half = (p - 1) // 2
    y_of_d = {}
    for (x, yy), d in dl.items():
        if d:
            y_of_d[d] = yy
    c = [0] * n
    for d in range(1, n):
        yy = y_of_d[d]
        c[d] = 1 if pow(yy, half, p) == 1 else -1

    # -- mu6 orbit reps on (Z/n)*, identical rule to run_n1_120deg_v1.mu6_reps
    m2 = m * m % n
    U  = [1, n - 1, m, n - m, m2, n - m2]    # {1,-1,m,-m,m^2,-m^2}
    seen = [False] * n
    reps = []
    for d in range(1, n):
        if seen[d]:
            continue
        reps.append(d)
        for u in U:
            seen[d * u % n] = True
    L = len(reps)
    assert L == (n - 1) // 6, (n, L, (n - 1) // 6)

    # -- the reduced sequence u on Q6 (indexed by coset-rep position)
    u = [c[r] for r in reps]
    d_to_q6idx = {}
    for j, r in enumerate(reps):
        for uu in U:
            d_to_q6idx[r * uu % n] = j

    g = primitive_root(n)

    return dict(n=n, m=m, eps=eps, g=g, L=L, u=u, reps=reps,
                d_to_q6idx=d_to_q6idx, c=c)


def inv_mod(a, n):
    return pow(a, n - 2, n)           # n prime


# ============================================================================
# Probe A -- subgroup-restricted partial sums on Q6
# ============================================================================
def probe_a(L, u, rng):
    """For each small prime q | L, 2 <= q <= min(L//2, QCAP):
       partition Q6 into q cosets of its index-q subgroup; statistic = max |sum over coset|.
       Returns list of (q, obs, rank, coset_size)."""
    qs = []
    tt = L
    d = 2
    while d * d <= tt:
        if tt % d == 0:
            if 2 <= d <= min(L // 2, PROBE_A_QCAP):
                qs.append(d)
            while tt % d == 0:
                tt //= d
        d += 1
    if tt > 1 and 2 <= tt <= min(L // 2, PROBE_A_QCAP):
        qs.append(tt)
    qs = sorted(set(qs))
    if not qs:
        return []

    results = []
    for q in qs:
        w = L // q
        if w < 2:
            continue
        obs = max(abs(sum(u[r + k * q] for k in range(w))) for r in range(q))
        rank = 0
        for _ in range(R_NULL):
            rnd = [rng.choice((-1, 1)) for _ in range(L)]
            null_max = max(abs(sum(rnd[r + k * q] for k in range(w))) for r in range(q))
            if null_max < obs:
                rank += 1
        results.append((q, obs, rank, w))
    return results


def probe_a_plant_control(L, u, rng):
    """Plant a coset-0 bias at strength PLANT_NUM/PLANT_DEN; return (q, obs, rank) or None."""
    q = None
    for qq in (2, 3, 5, 7, 11):
        if L % qq == 0 and L // qq >= 4:
            q = qq
            break
    if q is None:
        return None
    w = L // q
    planted = list(u)
    coset0 = [k * q for k in range(w)]
    rng.shuffle(coset0)
    n_force = w * PLANT_NUM // PLANT_DEN
    for idx in coset0[:n_force]:
        planted[idx] = 1
    obs = abs(sum(planted[k * q] for k in range(w)))
    rank = 0
    for _ in range(R_NULL):
        rnd = [rng.choice((-1, 1)) for _ in range(L)]
        null_max = max(abs(sum(rnd[r + k * q] for k in range(w))) for r in range(q))
        if null_max < obs:
            rank += 1
    return (q, obs, rank)


# ============================================================================
# Probe B -- d^{-1} involution + d^k maps on Q6  (the non-algebraic channel)
# ============================================================================
def build_q6_involution(n, m, reps, d_to_q6idx):
    """Map d -> d^{-1} descends to an involution iota on Q6 (m^{-1} has order 3)."""
    L = len(reps)
    iota = [0] * L
    for j, r in enumerate(reps):
        rin = inv_mod(r, n)
        iota[j] = d_to_q6idx[rin]
    return iota


def build_q6_powk_map(n, reps, d_to_q6idx, k):
    """Map d -> d^k descends to a permutation rho_k on Q6 iff gcd(k,6)=1."""
    if math.gcd(k, 6) != 1:
        return None
    L = len(reps)
    rho = [0] * L
    for j, r in enumerate(reps):
        rho[j] = d_to_q6idx[pow(r, k, n)]
    if sorted(rho) != list(range(L)):
        return None
    return rho


def probe_b_autocorr(L, u, perm):
    """Statistic: sum_j u[j] * u[perm[j]].  Exact integer."""
    return sum(u[j] * u[perm[j]] for j in range(L))


def probe_b_null_rank(L, u, perm, obs, rng):
    """Null: permute the VALUES of u uniformly over the L positions; rank |obs| among nulls."""
    vals = list(u)
    rank = 0
    for _ in range(R_NULL):
        rng.shuffle(vals)
        null_val = sum(vals[j] * vals[perm[j]] for j in range(L))
        if abs(null_val) < abs(obs):
            rank += 1
    return rank


def probe_b_plant_control(L, u, perm, rng):
    """Plant an involution-aligned signal; return (obs, rank) or None."""
    seen = [False] * L
    pairs = []
    for j in range(L):
        if seen[j]:
            continue
        jj = perm[j]
        if jj == j:
            seen[j] = True
            continue
        pairs.append((j, jj))
        seen[j] = True
        seen[jj] = True
    if not pairs:
        return None
    rng.shuffle(pairs)
    n_force = len(pairs) * PLANT_NUM // PLANT_DEN
    planted = list(u)
    for (a, b) in pairs[:n_force]:
        planted[a] = 1
        planted[b] = 1
    obs = sum(planted[j] * planted[perm[j]] for j in range(L))
    vals = list(planted)
    rank = 0
    for _ in range(R_NULL):
        rng.shuffle(vals)
        null_val = sum(vals[j] * vals[perm[j]] for j in range(L))
        if abs(null_val) < abs(obs):
            rank += 1
    return (obs, rank)


# ============================================================================
# Probe C -- incomplete-sum concentration at controlled aperture
# ============================================================================
def probe_c(L, u, rng):
    """For each window length w, slide across Q6 and take max |sum over circular window|."""
    ws = [w for w in PROBE_C_WS if 2 <= w <= L // 4]
    results = []
    for w in ws:
        best = 0
        for start in range(L):
            s = sum(u[(start + t) % L] for t in range(w))
            a = abs(s)
            if a > best:
                best = a
        rank = 0
        for _ in range(R_NULL):
            rnd = [rng.choice((-1, 1)) for _ in range(L)]
            null_best = 0
            for start in range(L):
                s = sum(rnd[(start + t) % L] for t in range(w))
                a = abs(s)
                if a > null_best:
                    null_best = a
            if null_best < best:
                rank += 1
        results.append((w, best, rank))
    return results


def probe_c_plant_control(L, u, rng):
    """Plant a window-0 bias; return (w, obs, rank) or None."""
    w = None
    for ww in PROBE_C_WS:
        if ww <= L // 4:
            w = ww            # largest admissible w
    if w is None:
        return None
    planted = list(u)
    window = list(range(w))
    rng.shuffle(window)
    n_force = w * PLANT_NUM // PLANT_DEN
    for idx in window[:n_force]:
        planted[idx] = 1
    obs = abs(sum(planted[:w]))
    rank = 0
    for _ in range(R_NULL):
        rnd = [rng.choice((-1, 1)) for _ in range(L)]
        null_best = abs(sum(rnd[:w]))
        if null_best < obs:
            rank += 1
    return (w, obs, rank)


# ============================================================================
# main driver
# ============================================================================
def run_prime(p, stratum_label):
    """Run all three probes + controls for one prime."""
    q6 = build_q6(p)
    if q6 is None:
        print("  SKIP: build_q6 returned None (n not prime or 6 -| n-1)")
        return None
    n   = q6["n"]
    m   = q6["m"]
    eps = q6["eps"]
    L   = q6["L"]
    u   = q6["u"]
    reps = q6["reps"]
    d_to_q6idx = q6["d_to_q6idx"]
    c   = q6["c"]

    # verify forced symmetries
    sym3_ok = all(c[m * d % n] == c[d] for d in range(1, n))
    symn_ok = all(c[(-d) % n] == eps * c[d] for d in range(1, n))

    rng = random.Random(SEED + p)

    print("  forced symmetries: mu3-invar %s, negation %s" % (sym3_ok, symn_ok))
    if not (sym3_ok and symn_ok):
        print("  ABORT: forced symmetry verification FAILED")
        return None

    a_results = probe_a(L, u, rng)
    a_ctrl    = probe_a_plant_control(L, u, rng)

    iota = build_q6_involution(n, m, reps, d_to_q6idx)
    b_inv_obs  = probe_b_autocorr(L, u, iota)
    b_inv_rank = probe_b_null_rank(L, u, iota, b_inv_obs, rng)
    b_inv_ctrl = probe_b_plant_control(L, u, iota, rng)
    b_k_results = []
    for k in PROBE_B_KS:
        rho = build_q6_powk_map(n, reps, d_to_q6idx, k)
        if rho is None:
            continue
        obs  = probe_b_autocorr(L, u, rho)
        rank = probe_b_null_rank(L, u, rho, obs, rng)
        b_k_results.append((k, obs, rank))

    c_results = probe_c(L, u, rng)
    c_ctrl    = probe_c_plant_control(L, u, rng)

    return dict(p=p, n=n, L=L, eps=eps, m=m,
                sym3=sym3_ok, symn=symn_ok,
                a_results=a_results, a_ctrl=a_ctrl,
                b_inv_obs=b_inv_obs, b_inv_rank=b_inv_rank, b_inv_ctrl=b_inv_ctrl,
                b_k_results=b_k_results,
                c_results=c_results, c_ctrl=c_ctrl,
                stratum=stratum_label)


def _mark(rank):
    if is_hit(rank):
        return " <<<"
    if is_fire(rank):
        return " *"
    return ""


def report(res):
    print("  --- Probe A (subgroup-restricted partial sums) ---")
    if res["a_results"]:
        for (q, obs, rank, w) in res["a_results"]:
            print("    q=%-4d cosetsize=%-4d  max|sum|=%-6d  rank %4d/%d%s" %
                  (q, w, obs, rank, R_NULL, _mark(rank)))
    else:
        print("    (no small-prime divisors q of L=%d in range)" % res["L"])
    if res["a_ctrl"]:
        q, obs, rank = res["a_ctrl"]
        ok = "FIRE" if is_fire(rank) else "FAIL"
        print("    PLANT(q=%d,f=3/10): max|sum|=%-6d rank %4d/%d  [%s]" % (q, obs, rank, R_NULL, ok))

    print("  --- Probe B (non-algebraic channel: d^{-1} and d^k) ---")
    print("    d^{-1} involution: T=%+d  rank %4d/%d%s" %
          (res["b_inv_obs"], res["b_inv_rank"], R_NULL, _mark(res["b_inv_rank"])))
    if res["b_inv_ctrl"]:
        obs, rank = res["b_inv_ctrl"]
        ok = "FIRE" if is_fire(rank) else "FAIL"
        print("    PLANT(d^{-1},f=3/10): T=%+d rank %4d/%d  [%s]" % (obs, rank, R_NULL, ok))
    for (k, obs, rank) in res["b_k_results"]:
        print("    d^%-2d map:         T=%+d  rank %4d/%d%s" % (k, obs, rank, R_NULL, _mark(rank)))

    print("  --- Probe C (incomplete-sum aperture) ---")
    for (w, obs, rank) in res["c_results"]:
        print("    w=%-4d  max|sum|=%-6d  rank %4d/%d%s" % (w, obs, rank, R_NULL, _mark(rank)))
    if res["c_ctrl"]:
        w, obs, rank = res["c_ctrl"]
        ok = "FIRE" if is_fire(rank) else "FAIL"
        print("    PLANT(w=%d,f=3/10): max|sum|=%-6d rank %4d/%d  [%s]" % (w, obs, rank, R_NULL, ok))
    print()


def main():
    print("=" * 92)
    print("mu3_subspace_residual_v1  --  three probes on the mu3-forced subspace residual")
    print("PREREG: PREREG_mu3_subspace_residual_v1.md  |  R_NULL=%d  SEED=%d" % (R_NULL, SEED))
    print("Float-free signal path; float only in monotone statistic ranked vs permutation null.")
    print("=" * 92)
    all_results = []
    for label, plist in (("IN", PRIMES_IN), ("S", PRIMES_S), ("C", PRIMES_C)):
        print("\n=== stratum %s ===" % label)
        for p in plist:
            print("\np = %d" % p)
            res = run_prime(p, label)
            if res is None:
                continue
            report(res)
            all_results.append(res)

    # ---- summary ----
    print("\n" + "=" * 92)
    print("SUMMARY  (rank >= 99%%*R = '<<<';  >= 95%%*R = '*')")
    print("=" * 92)
    print("\nProbe B (d^{-1} involution) -- the structural prediction:")
    print("%-6s %-4s %-6s | %-10s %-10s" % ("p", "str", "L", "T_inv", "rank"))
    for r in all_results:
        print("%-6d %-4s %-6d | %+10d %4d/%d%s" %
              (r["p"], r["stratum"], r["L"], r["b_inv_obs"], r["b_inv_rank"], R_NULL,
               _mark(r["b_inv_rank"])))

    print("\nProbe B (d^k maps) -- percentile ranks:")
    all_ks = sorted(set(k for r in all_results for (k, _, _) in r["b_k_results"]))
    if all_ks:
        hdr = "%-6s %-4s %-6s |" % ("p", "str", "L") + "".join(" d^%-2d" % k for k in all_ks)
        print(hdr)
        for r in all_results:
            rankmap = {k: rk for (k, _, rk) in r["b_k_results"]}
            line = "%-6d %-4s %-6d |" % (r["p"], r["stratum"], r["L"])
            for k in all_ks:
                rk = rankmap.get(k)
                if rk is None:
                    line += "   - "
                else:
                    pct = rk * 100 // R_NULL
                    mk = "<" if is_hit(rk) else (">" if is_fire(rk) else " ")
                    line += " %3d%s" % (pct, mk)
            print(line)

    print("\nProbe A (subgroup-restricted sums) -- count of q-values at FIRE/HIT:")
    print("%-6s %-4s | hits/total" % ("p", "str"))
    for r in all_results:
        total = len(r["a_results"])
        hits  = sum(1 for (_, _, rank, _) in r["a_results"] if is_fire(rank))
        print("%-6d %-4s | %d/%d" % (r["p"], r["stratum"], hits, total))

    print("\nProbe C (aperture) -- count of w-values at FIRE/HIT:")
    print("%-6s %-4s | hits/total" % ("p", "str"))
    for r in all_results:
        total = len(r["c_results"])
        hits  = sum(1 for (_, _, rank) in r["c_results"] if is_fire(rank))
        print("%-6d %-4s | %d/%d" % (r["p"], r["stratum"], hits, total))

    # ---- control validity check ----
    print("\n" + "-" * 60)
    print("CONTROL VALIDITY (any FAIL => instrument invalid at that prime)")
    ctrl_fail = False
    for r in all_results:
        fails = []
        if r["a_ctrl"] and not is_fire(r["a_ctrl"][2]):
            fails.append("A-plant")
        if r["b_inv_ctrl"] and not is_fire(r["b_inv_ctrl"][1]):
            fails.append("B-plant")
        if r["c_ctrl"] and not is_fire(r["c_ctrl"][2]):
            fails.append("C-plant")
        if fails:
            ctrl_fail = True
            print("  p=%-6d %s: CONTROL FAIL %s" % (r["p"], r["stratum"], ",".join(fails)))
    if not ctrl_fail:
        print("  all firing controls PASSED at every prime.")


if __name__ == "__main__":
    main()
