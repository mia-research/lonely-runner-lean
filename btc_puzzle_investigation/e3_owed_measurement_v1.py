#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
e3_owed_measurement_v1.py -- executes FROZEN PREREG_e3_owed_measurement_v2.md, arms A1-A4.
Discharges MASTER_v12 §E.3 / ROADMAP_REDIRECT_v3 Brick A.

Integer-exact signal path (int + gmpy2.powmod). Structural (generator-free) null = uniform random
valid secp curve x-coords. NO floating point decides any verdict; floats appear only in printed pctiles.
Frozen: N_null=20000 seed 20260818 (null & OOS), A4 seed 12345.

Usage: python3 e3_owed_measurement_v1.py [N_null] [M_oos]   (defaults = frozen 20000, 1000)
"""
import sys, csv, random, json, time
try:
    from gmpy2 import mpz, powmod
    def _pw(z, e, m): return int(powmod(mpz(z), e, m))
    FAST = True
except Exception:
    def _pw(z, e, m): return pow(int(z), e, m)
    FAST = False

# ---- secp256k1 field + cubic/quadratic character constants ----
P     = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Bc    = 7                     # y^2 = x^3 + 7
BETA  = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA2 = pow(BETA, 2, P)
E2EXP = (P - 1) // 2          # quadratic (Legendre) exponent
E3EXP = (P - 1) // 3          # cubic exponent
BASE  = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
SCR   = "/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/0e15b049-3ab5-4bd7-bf73-9254eef70733/scratchpad"

def cube_class(z):            # z != 0 mod P ; returns 0/1/2
    r = _pw(z, E3EXP, P)
    return 0 if r == 1 else (1 if r == BETA else (2 if r == BETA2 else -1))

def qr_bit(z):                # 0 if QR, 1 if QNR ; z != 0
    return 0 if _pw(z, E2EXP, P) == 1 else 1

def field_diff_hist(xs):      # 6-cell H[3q+c] over all C(n,2) field differences
    H = [0] * 6
    n = len(xs)
    for i in range(n):
        xi = xs[i]
        for j in range(i + 1, n):
            z = (xi - xs[j]) % P
            if z == 0:
                raise ValueError("coincident x (z=0) -- cubic class undefined")
            H[3 * qr_bit(z) + cube_class(z)] += 1
    return H

def stats3(H):                # (E2, E3, E6) -- verbatim from c2_grouplaw_diffset_curve_v1.py
    nb0 = H[0] + H[1] + H[2]; nb1 = H[3] + H[4] + H[5]
    E2 = (nb0 - nb1) ** 2
    nc0 = H[0] + H[3]; nc1 = H[1] + H[4]; nc2 = H[2] + H[5]
    A3 = nc0 - nc2; B3 = nc1 - nc2; E3 = A3 * A3 - A3 * B3 + B3 * B3
    nm = [H[0], H[5], H[1], H[3], H[2], H[4]]
    A6 = nm[0] - nm[2] - nm[3] + nm[5]; B6 = nm[1] + nm[2] - nm[4] - nm[5]
    E6 = A6 * A6 + A6 * B6 + B6 * B6
    return E2, E3, E6

def cube_marginals(H):        # (a,b,c) = cube-class counts, for A4 plant
    return H[0] + H[3], H[1] + H[4], H[2] + H[5]

def E3_from_counts(a, b, c):
    return a * a + b * b + c * c - a * b - b * c - c * a

def rand_curve_x(rng):        # uniform random valid secp E(F_P) x-coord (generator-free structural null)
    while True:
        x = rng.randrange(0, P)
        rhs = (x * x % P * x + Bc) % P
        if rhs == 0:
            continue
        if _pw(rhs, E2EXP, P) == 1:   # rhs is a QR -> x is a real curve point x-coord
            return x

def p_num(sorted_null, v, N):
    # INTEGER numerator of the two-sided rank p over the common denominator (N+1), capped at (N+1)=p<=1.
    # symmetric +1 on BOTH tails (PREREG v2 fix); inclusive >= / <= ties. All comparisons stay integer.
    import bisect
    ge = N - bisect.bisect_left(sorted_null, v)     # #{null >= v}
    le = bisect.bisect_right(sorted_null, v)         # #{null <= v}
    return min(N + 1, 2 * min(ge + 1, le + 1))

def p_disp(num, N):                                  # DISPLAY-ONLY float of an integer p-numerator
    return num / (N + 1)

def pctile(sorted_null, v, N):                       # DISPLAY-ONLY percentile
    import bisect
    return bisect.bisect_right(sorted_null, v) / N * 100.0

def main():
    N_null = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    M_oos  = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    SEED_NULL, SEED_A4 = 20260818, 12345
    FROZEN = (N_null == 20000 and M_oos == 1000)
    t0 = time.perf_counter()
    print("=" * 84)
    print(f"E3 OWED MEASUREMENT (PREREG v2, A1-A4)  gmpy2={FAST}  N_null={N_null} M_oos={M_oos}  "
          f"{'[FROZEN RUN]' if FROZEN else '[SMOKE/bug-check -- NOT the frozen decision]'}")
    print("=" * 84)

    # ---------- real 82 (fixed object) ----------
    real = []
    with open(f"{BASE}/solved_puzzles_xy.csv") as f:
        for r in csv.DictReader(f):
            real.append((int(r["bits"]), int(r["X"], 16)))
    real.sort(key=lambda t: t[0])
    real_bits = [b for b, _ in real]
    xs_real = [x for _, x in real]
    assert len(xs_real) == 82
    H_real = field_diff_hist(xs_real)
    a_r, b_r, c_r = cube_marginals(H_real)
    E2_r, E3_r, E6_r = stats3(H_real)
    print(f"[integrity] cube counts (a,b,c)=({a_r},{b_r},{c_r}) sum={a_r+b_r+c_r}  "
          f"E2={E2_r} E3={E3_r} E6={E6_r}  E3%3={E3_r%3}")
    assert (a_r, b_r, c_r) == (1082, 1057, 1182) and E3_r == 13125 and a_r+b_r+c_r == 3321 and E3_r % 3 == 0, \
        "INTEGRITY FAIL -- object mismatch, abort"
    print("[integrity] OK -- fixed object E3(real)=13125 reproduced exactly")

    # ---------- A1/A2: structural null ----------
    print(f"\n[A1/A2] building structural null (uniform secp curve points), N={N_null}, seed={SEED_NULL} ...")
    rng = random.Random(SEED_NULL)
    nE2, nE3, nE6 = [], [], []
    nABC = []
    for i in range(N_null):
        xs = [rand_curve_x(rng) for _ in range(82)]
        H = field_diff_hist(xs)
        e2, e3, e6 = stats3(H)
        nE2.append(e2); nE3.append(e3); nE6.append(e6); nABC.append(cube_marginals(H))
        if (i + 1) % 2000 == 0:
            print(f"   null {i+1}/{N_null}  ({time.perf_counter()-t0:.0f}s)", flush=True)
    sE2, sE3, sE6 = sorted(nE2), sorted(nE3), sorted(nE6)

    # order-statistic boundaries as INTEGER indices (no float touches the verdict)
    L_struct = sE3[(25 * N_null) // 1000]
    U_struct = sE3[(975 * N_null) // 1000]
    pnum_struct = p_num(sE3, E3_r, N_null)
    pct_E3 = pctile(sE3, E3_r, N_null)
    reject_high = E3_r > U_struct                    # INTEGER decision
    print(f"\n########## A1 -- structural null decision ##########")
    print(f"null E3: mean~{sum(nE3)//N_null}  min/med/max={sE3[0]}/{sE3[N_null//2]}/{sE3[-1]}")
    print(f"frozen region [L_struct,U_struct] = [{L_struct}, {U_struct}]  (reject-high iff E3>U)")
    print(f"E3(real)={E3_r}  ->  {'REJECT-HIGH' if reject_high else 'FAIL-TO-REJECT'}"
          f"   pctile={pct_E3:.2f}   two-sided p_struct={p_disp(pnum_struct,N_null):.5f}")

    # A2 FWER (Westfall-Young max-stat / min-p over {E2,E3,E6}) -- INTEGER p-numerators throughout
    pn_E2o = p_num(sE2, E2_r, N_null)
    pn_E3o = p_num(sE3, E3_r, N_null)
    pn_E6o = p_num(sE6, E6_r, N_null)
    minpn_real = min(pn_E2o, pn_E3o, pn_E6o)
    cnt = 0
    for i in range(N_null):
        mpn = min(p_num(sE2, nE2[i], N_null),
                  p_num(sE3, nE3[i], N_null),
                  p_num(sE6, nE6[i], N_null))
        if mpn <= pn_E3o:                            # INTEGER comparison (common denom)
            cnt += 1
    p_FWER_E3 = (cnt + 1) / (N_null + 1)             # display float
    fwer_sig = (cnt + 1) * 20 <= (N_null + 1)        # INTEGER decision: p_FWER <= 1/20
    bonf7_num = min(N_null + 1, 7 * pnum_struct)
    print(f"\n########## A2 -- family-wise (E2,E3,E6) Westfall-Young ##########")
    print(f"per-stat two-sided p: E2={p_disp(pn_E2o,N_null):.5f}  E3={p_disp(pn_E3o,N_null):.5f}  "
          f"E6={p_disp(pn_E6o,N_null):.5f}   min-p(real)={p_disp(minpn_real,N_null):.5f}")
    print(f"p_FWER(E3) = {p_FWER_E3:.5f}   (Bonferroni x7 of raw p_struct = {p_disp(bonf7_num,N_null):.4f})")
    print(f"decision: {'family-wise SIGNIFICANT (p_FWER<=0.05)' if fwer_sig else 'family-wise NON-significant (bounded magnitude)'}")

    # ---------- A3: OOS on band-matched known-MT sets ----------
    print(f"\n[A3] loading constructed known-MT pool by bit-length ...")
    pool = {}
    with open(f"{BASE}/constructed_keys_1to160_100k.csv") as f:
        for r in csv.DictReader(f):
            pool.setdefault(int(r["bits"]), []).append(int(r["X"], 16))
    missing = [b for b in real_bits if b not in pool or len(pool[b]) == 0]
    print(f"   pool bits covered: {sorted(pool)[:5]}... ; real bits missing from pool: {missing}")
    rng3 = random.Random(SEED_NULL)
    mtE3 = []
    for t in range(M_oos):
        xs = [rng3.choice(pool[b]) for b in real_bits]
        mtE3.append(stats3(field_diff_hist(xs))[1])
        if (t + 1) % 200 == 0:
            print(f"   oos {t+1}/{M_oos}  ({time.perf_counter()-t0:.0f}s)", flush=True)
    hits_MT = sum(1 for v in mtE3 if v >= E3_r)      # INTEGER
    q_MT = hits_MT / M_oos                            # display
    mt_med = sorted(mtE3)[M_oos // 2]
    mt_med_pct = pctile(sE3, mt_med, N_null)
    if hits_MT * 20 <= M_oos:                         # q_MT <= 0.05
        a3 = "SET-SPECIFIC (real high even among band-matched MT sets)"
    elif hits_MT * 2 <= M_oos:                        # q_MT <= 0.50
        a3 = f"PARTIAL (real above {(M_oos-hits_MT)*100//M_oos}% of band-matched MT sets)"
    else:
        a3 = "PIPELINE/BIT-BAND (real typical of/below band-matched MT sets)"
    print(f"\n########## A3 -- OOS on band-matched known-MT sets ##########")
    print(f"MT-set E3: min/med/max={sorted(mtE3)[0]}/{mt_med}/{sorted(mtE3)[-1]}  "
          f"(median at {mt_med_pct:.1f}th pctile of structural null)")
    print(f"q_MT = #{{MT-set E3 >= {E3_r}}}/{M_oos} = {q_MT:.4f}   ->  {a3}")

    # ---------- A4: firing control (marginal beta^2-count plant) ----------
    print(f"\n########## A4 -- firing control (beta^2-count plant, seed {SEED_A4}) ##########")
    rng4 = random.Random(SEED_A4)
    base_idx = list(range(N_null))
    fpr = None
    for D in (0, 25, 50, 75, 100, 150):
        hits = 0; NREP = 500
        pick = rng4.sample(base_idx, min(NREP, N_null))
        for idx in pick:
            a, b, c = nABC[idx]
            a2 = a - (D // 2); b2 = b - (D - D // 2); c2 = c + D   # move D pairs into class beta^2 (c)
            if E3_from_counts(a2, b2, c2) > U_struct:
                hits += 1
        pw = hits / len(pick)
        if D == 0:
            fpr = pw
        print(f"   Delta={D:>3}: reject-high power = {pw:.3f}  ({hits}/{len(pick)})")
    print(f"   [gate] Delta=0 FPR={fpr:.3f} (nominal ~0.025 one-sided); expect monotone, >=0.9 by Delta=150")

    # ---------- persist ----------
    if FROZEN:
        import numpy as np
        np.save(f"{BASE}/e3_struct_null_E3_v1.npy", np.array(nE3, dtype=np.int64))
        np.save(f"{BASE}/e3_struct_null_E2_v1.npy", np.array(nE2, dtype=np.int64))
        np.save(f"{BASE}/e3_struct_null_E6_v1.npy", np.array(nE6, dtype=np.int64))
        summary = dict(prereg="PREREG_e3_owed_measurement_v2.md", N_null=N_null, M_oos=M_oos,
                       seed_null=SEED_NULL, seed_a4=SEED_A4,
                       E2_real=E2_r, E3_real=E3_r, E6_real=E6_r, abc_real=[a_r, b_r, c_r],
                       L_struct=L_struct, U_struct=U_struct, reject_high=bool(reject_high),
                       pctile_E3=pct_E3, p_struct=p_disp(pnum_struct, N_null),
                       p_E2=p_disp(pn_E2o, N_null), p_E3=p_disp(pn_E3o, N_null),
                       p_E6=p_disp(pn_E6o, N_null), p_FWER_E3=p_FWER_E3, fwer_significant=bool(fwer_sig),
                       bonferroni7=p_disp(bonf7_num, N_null),
                       q_MT=q_MT, q_MT_hits=hits_MT, mt_med_E3=mt_med, mt_med_pctile=mt_med_pct, A4_fpr=fpr)
        with open(f"{BASE}/e3_owed_measurement_v1_summary.json", "w") as jf:
            json.dump(summary, jf, indent=2)
        print(f"\n[persist] nulls + summary written.")
    print(f"\nDONE ({time.perf_counter()-t0:.0f}s).")

if __name__ == "__main__":
    main()
