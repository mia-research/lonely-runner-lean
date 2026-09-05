#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
grouplaw_e3_real82_v1.py -- executes FROZEN PREREG_grouplaw_e3_real82_v1.md, arms A1-A5.
Group-law difference-set E3 = cubic-character energy of {x(Pi-Pj)} on the real 82 pubkey POINTS
(CM-native: uses y via curve addition). Named next probe of RESULT_e3_owed_measurement_v1 (Brick A).

Curve/stats3/diffset_hist copied VERBATIM from the validated c2_grouplaw_diffset_curve_v1.py.
Integer-exact signal + DECISION path (order-stat indices, integer p-numerators, integer thresholds);
floats are display-only. Frozen: N_null=10000 seed 20260818 (null & OOS), A4 seed 12345.

Usage: python3 grouplaw_e3_real82_v1.py [N_null] [M_oos]   (defaults = frozen 10000, 1000)
"""
import sys, csv, random, json, time, bisect

P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE
BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"

# ---- Curve: copied verbatim from c2_grouplaw_diffset_curve_v1.py (secp branch) ----
class Curve:
    def __init__(self):
        self.p = P; self.a = 0; self.b = 7
        self.beta = BETA
        assert self.p % 4 == 3
        self.e2 = (self.p - 1) // 2
        self.has3 = (self.p % 3 == 1); self.e3 = (self.p - 1) // 3
        self.sqrtexp = (self.p + 1) // 4
        W = next(t for z in range(2, 100) if (t := pow(z, self.e3, self.p)) != 1)
        self.cube = {1: 0, W: 1, (W * W) % self.p: 2}

    def add(self, Pp, Qq):
        if Pp is None: return Qq
        if Qq is None: return Pp
        x1, y1 = Pp; x2, y2 = Qq; p = self.p
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            lam = (3 * x1 * x1 + self.a) % p * pow(2 * y1 % p, -1, p) % p
        else:
            lam = (y2 - y1) % p * pow((x2 - x1) % p, -1, p) % p
        x3 = (lam * lam - x1 - x2) % p
        return (x3, (lam * (x1 - x3) - y1) % p)

    def rand_point(self, rng):
        p = self.p
        while True:
            x = rng.randrange(1, p)
            rhs = (x * x % p * x + self.a * x + self.b) % p
            if rhs == 0 or pow(rhs, self.e2, p) != 1: continue
            y = pow(rhs, self.sqrtexp, p)
            return (x, p - y if rng.getrandbits(1) else y)

    def code(self, x):
        b = 0 if pow(x % self.p, self.e2, self.p) == 1 else 1
        c = self.cube[pow(x % self.p, self.e3, self.p)]
        return 3 * b + c

    def gl_diff_code(self, Pi, Pj):
        xj, yj = Pj
        D = self.add(Pi, (xj, (self.p - yj) % self.p))
        return None if D is None else self.code(D[0])

def stats3(H):                    # verbatim
    nb0 = H[0] + H[1] + H[2]; nb1 = H[3] + H[4] + H[5]
    E2 = (nb0 - nb1) ** 2
    nc0 = H[0] + H[3]; nc1 = H[1] + H[4]; nc2 = H[2] + H[5]
    A3 = nc0 - nc2; B3 = nc1 - nc2; E3 = A3 * A3 - A3 * B3 + B3 * B3
    nm = [H[0], H[5], H[1], H[3], H[2], H[4]]
    A6 = nm[0] - nm[2] - nm[3] + nm[5]; B6 = nm[1] + nm[2] - nm[4] - nm[5]
    E6 = A6 * A6 + A6 * B6 + B6 * B6
    return E2, E3, E6

def diffset_hist(cur, pts):       # verbatim
    H = [0] * 6
    for i in range(len(pts)):
        Pi = pts[i]
        for j in range(i + 1, len(pts)):
            c = cur.gl_diff_code(Pi, pts[j])
            if c is not None: H[c] += 1
    return H

def cube_marginals(H): return H[0] + H[3], H[1] + H[4], H[2] + H[5]
def E3_from_counts(a, b, c): return a * a + b * b + c * c - a * b - b * c - c * a

# ---- INTEGER decision helpers (no float touches a verdict) ----
def p_num(sorted_null, v, N):     # integer numerator of two-sided rank p over common denom (N+1), capped
    ge = N - bisect.bisect_left(sorted_null, v)   # #{null >= v}
    le = bisect.bisect_right(sorted_null, v)       # #{null <= v}
    return min(N + 1, 2 * min(ge + 1, le + 1))
def p_disp(num, N): return num / (N + 1)           # DISPLAY only
def pctile(sorted_null, v, N): return bisect.bisect_right(sorted_null, v) / N * 100.0  # DISPLAY only

def main():
    N_null = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    M_oos  = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    SEED_NULL, SEED_A4 = 20260818, 12345
    FROZEN = (N_null == 10000 and M_oos == 1000)
    t0 = time.perf_counter()
    cur = Curve()
    print("=" * 88)
    print(f"GROUP-LAW E3 on the real 82 (PREREG grouplaw_e3_real82_v1, A1-A5)  "
          f"N_null={N_null} M_oos={M_oos}  {'[FROZEN]' if FROZEN else '[SMOKE -- not the frozen decision]'}")
    print("=" * 88)

    # ---------- A5 (run first): C-GLV forced-structure control ----------
    rng5 = random.Random(999)
    orb = []
    for _ in range(27):                              # 27 orbits x3 = 81 phi-closed points
        x, y = cur.rand_point(rng5)
        orb += [(x, y), (BETA * x % P, y), (BETA * BETA % P * x % P, y)]
    E2c, E3c, E6c = stats3(diffset_hist(cur, orb))
    print(f"\n########## A5 -- C-GLV forced-structure control ##########")
    print(f"phi-closed 81-set:  E2={E2c}  E3={E3c}  E6={E6c}   (expect E3=E6=0 exact, E2!=0)")
    assert E3c == 0 and E6c == 0 and E2c != 0, "C-GLV FAIL -- harness/object bug (phi-closed must zero E3,E6)"
    print("C-GLV PASS -- statistic is zeroed by exact cubic symmetry; a nonzero E3 reads genuine imbalance")

    # ---------- real 82 points (fixed object) ----------
    real = []
    with open(f"{BASE}/solved_puzzles_xy.csv") as f:
        for r in csv.DictReader(f):
            real.append((int(r["bits"]), (int(r["X"], 16), int(r["Y"], 16))))
    real.sort(key=lambda t: t[0])
    real_bits = [b for b, _ in real]
    pts_real = [pt for _, pt in real]
    assert len(pts_real) == 82
    for (x, y) in pts_real:
        assert (y * y - (x * x % P * x + 7)) % P == 0, "real point not on curve"
    H_real = diffset_hist(cur, pts_real)
    T_real = sum(H_real)
    a_r, b_r, c_r = cube_marginals(H_real)
    E2_r, E3_r, E6_r = stats3(H_real)
    print(f"\n[integrity] gl-diff cube counts (a,b,c)=({a_r},{b_r},{c_r})  T={T_real}  "
          f"E2={E2_r} E3={E3_r} E6={E6_r}  E3%3={E3_r%3}")
    assert T_real == 3321, f"T={T_real} (expected 3321 -- an infinity/coincidence appeared)"
    assert E3_r % 3 == 0, "E3 not ≡0 mod3 though T≡0 mod3 -- path bug"
    assert E3_r > 0, "real E3 forced 0 -- real set would be phi-closed (it is not)"
    print(f"[integrity] OK -- real gl-diff object built; E3_gl(real)={E3_r} (>0, NOT forced)")

    # ---------- A1/A2: structural null (uniform random curve points) ----------
    print(f"\n[A1/A2] building group-law structural null, N={N_null}, seed={SEED_NULL} ...")
    rng = random.Random(SEED_NULL)
    nE2, nE3, nE6, nABC = [], [], [], []
    for i in range(N_null):
        pts = [cur.rand_point(rng) for _ in range(82)]
        H = diffset_hist(cur, pts)
        e2, e3, e6 = stats3(H)
        nE2.append(e2); nE3.append(e3); nE6.append(e6); nABC.append(cube_marginals(H))
        if (i + 1) % 1000 == 0:
            print(f"   null {i+1}/{N_null}  ({time.perf_counter()-t0:.0f}s)", flush=True)
    sE2, sE3, sE6 = sorted(nE2), sorted(nE3), sorted(nE6)

    L_struct = sE3[(25 * N_null) // 1000]
    U_struct = sE3[(975 * N_null) // 1000]
    pnum_struct = p_num(sE3, E3_r, N_null)
    pct_E3 = pctile(sE3, E3_r, N_null)
    reject_high = E3_r > U_struct                    # INTEGER decision
    reject_low = E3_r < L_struct                     # INTEGER decision (low tail of the frozen two-sided test)
    verdict = "REJECT-HIGH" if reject_high else ("REJECT-LOW (over-uniformity)" if reject_low else "FAIL-TO-REJECT")
    print(f"\n########## A1 -- structural null decision ##########")
    print(f"null E3_gl: mean~{sum(nE3)//N_null}  min/med/max={sE3[0]}/{sE3[N_null//2]}/{sE3[-1]}")
    print(f"region [L,U]=[{L_struct}, {U_struct}]  (two-sided alpha=0.05: reject-high iff E3>U, reject-low iff E3<L)")
    print(f"E3_gl(real)={E3_r}  ->  {verdict}"
          f"   pctile={pct_E3:.2f}   two-sided p={p_disp(pnum_struct,N_null):.5f}")

    # A2 Westfall-Young FWER over {E2,E3,E6}, integer p-numerators
    pn_E2o = p_num(sE2, E2_r, N_null); pn_E3o = p_num(sE3, E3_r, N_null); pn_E6o = p_num(sE6, E6_r, N_null)
    cnt = 0
    for i in range(N_null):
        mpn = min(p_num(sE2, nE2[i], N_null), p_num(sE3, nE3[i], N_null), p_num(sE6, nE6[i], N_null))
        if mpn <= pn_E3o: cnt += 1
    p_FWER = (cnt + 1) / (N_null + 1)                 # display
    fwer_sig = (cnt + 1) * 20 <= (N_null + 1)         # INTEGER decision
    bonf7 = min(N_null + 1, 7 * pnum_struct)
    print(f"\n########## A2 -- family-wise (E2,E3,E6) Westfall-Young ##########")
    print(f"per-stat p: E2={p_disp(pn_E2o,N_null):.5f}  E3={p_disp(pn_E3o,N_null):.5f}  E6={p_disp(pn_E6o,N_null):.5f}")
    print(f"p_FWER(E3)={p_FWER:.5f}  (Bonferroni x7={p_disp(bonf7,N_null):.4f})  -> "
          f"{'family-wise SIGNIFICANT' if fwer_sig else 'family-wise NON-significant (bounded magnitude)'}")

    # ---------- A3: OOS band-matched known-MT points ----------
    print(f"\n[A3] loading constructed known-MT pool (X,Y) by bit-length ...")
    pool = {}
    with open(f"{BASE}/constructed_keys_1to160_100k.csv") as f:
        for r in csv.DictReader(f):
            pool.setdefault(int(r["bits"]), []).append((int(r["X"], 16), int(r["Y"], 16)))
    missing = [b for b in real_bits if b not in pool or not pool[b]]
    print(f"   real bits missing from pool: {missing}")
    rng3 = random.Random(SEED_NULL)
    mtE3 = []
    for t in range(M_oos):
        pts = [rng3.choice(pool[b]) for b in real_bits]
        mtE3.append(stats3(diffset_hist(cur, pts))[1])
        if (t + 1) % 200 == 0:
            print(f"   oos {t+1}/{M_oos}  ({time.perf_counter()-t0:.0f}s)", flush=True)
    hits_MT = sum(1 for v in mtE3 if v >= E3_r)       # INTEGER
    q_MT = hits_MT / M_oos                             # display
    mt_med = sorted(mtE3)[M_oos // 2]; mt_med_pct = pctile(sE3, mt_med, N_null)
    if hits_MT * 20 <= M_oos:   a3 = "SET-SPECIFIC (real high even among band-matched MT sets)"
    elif hits_MT * 2 <= M_oos:  a3 = f"PARTIAL (real above {(M_oos-hits_MT)*100//M_oos}% of band-matched MT sets)"
    else:                       a3 = "PIPELINE/BIT-BAND (real typical of/below band-matched MT sets)"
    print(f"\n########## A3 -- OOS band-matched known-MT points ##########")
    print(f"MT-set E3_gl: min/med/max={sorted(mtE3)[0]}/{mt_med}/{sorted(mtE3)[-1]} (median {mt_med_pct:.1f}th pct of null)")
    print(f"q_MT = {hits_MT}/{M_oos} = {q_MT:.4f}  ->  {a3}")

    # ---------- A4: firing control (beta^2-count plant) ----------
    print(f"\n########## A4 -- firing control (beta^2-count plant, seed {SEED_A4}) ##########")
    rng4 = random.Random(SEED_A4); fpr = None
    for D in (0, 25, 50, 75, 100, 150):
        pick = rng4.sample(range(N_null), min(500, N_null)); hits = 0
        for idx in pick:
            a, b, c = nABC[idx]
            if E3_from_counts(a - (D // 2), b - (D - D // 2), c + D) > U_struct: hits += 1
        pw = hits / len(pick)
        if D == 0: fpr = pw
        print(f"   Delta={D:>3}: power={pw:.3f} ({hits}/{len(pick)})")
    print(f"   [gate] Delta=0 FPR={fpr:.3f} (nominal ~0.025); expect monotone, >=0.9 by Delta=150")

    # ---------- persist ----------
    if FROZEN:
        import numpy as np
        np.save(f"{BASE}/gl_e3_struct_null_E3_v1.npy", np.array(nE3, dtype=np.int64))
        np.save(f"{BASE}/gl_e3_struct_null_E2_v1.npy", np.array(nE2, dtype=np.int64))
        np.save(f"{BASE}/gl_e3_struct_null_E6_v1.npy", np.array(nE6, dtype=np.int64))
        summary = dict(prereg="PREREG_grouplaw_e3_real82_v1.md", object="group-law diffset E3",
                       N_null=N_null, M_oos=M_oos, seed_null=SEED_NULL, seed_a4=SEED_A4,
                       cglv=dict(E2=E2c, E3=E3c, E6=E6c),
                       E2_real=E2_r, E3_real=E3_r, E6_real=E6_r, abc_real=[a_r, b_r, c_r], T_real=T_real,
                       L_struct=L_struct, U_struct=U_struct, reject_high=bool(reject_high),
                       reject_low=bool(reject_low), pctile_E3=pct_E3, p_struct=p_disp(pnum_struct, N_null),
                       p_E2=p_disp(pn_E2o, N_null), p_E3=p_disp(pn_E3o, N_null), p_E6=p_disp(pn_E6o, N_null),
                       p_FWER_E3=p_FWER, fwer_significant=bool(fwer_sig), bonferroni7=p_disp(bonf7, N_null),
                       q_MT=q_MT, q_MT_hits=hits_MT, mt_med_E3=mt_med, mt_med_pctile=mt_med_pct, A4_fpr=fpr,
                       field_diff_E3_for_comparison=13125)
        with open(f"{BASE}/grouplaw_e3_real82_v1_summary.json", "w") as jf:
            json.dump(summary, jf, indent=2)
        print(f"\n[persist] nulls + summary written.")
    print(f"\nDONE ({time.perf_counter()-t0:.0f}s).")

if __name__ == "__main__":
    main()
