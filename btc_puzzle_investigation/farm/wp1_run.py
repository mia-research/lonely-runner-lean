"""
WP1 -- The n*Q near-miss distinguisher (ATTACK-VALID).

Identity under test: for P = d*G with d = 2^(N-1) + floor(2^(N-1)*k/n) + D,
and Q = P - 2^(N-1)*G = P - Apt, the TRUE (n,k) satisfies

    n*Q - k*Apt = r*G,   r = n*D - (2^(N-1)*k mod n)

exactly (verified numerically against the dataset before this run: every
checked key reproduces this point equality). CORRECTION to the WP1 brief's
stated bound: the brief writes "|r| < 2^(N-1)/n"; that does not hold in
general -- |r| empirically tracks ~2^(N-1)/256 (a band-wide constant set by
the max_den=256 continued-fraction cutoff, not shrinking with n), with ~83%
of keys under that threshold and a heavier tail beyond it. The hash-table
radius used below is sized off the verified empirical constant, not the
brief's formula. So n*Q, reduced by the right multiple of Apt, is a
small-DL point for the TRUE n. For a wrong n', n'*Q is (conjectured) an
essentially random point EXCEPT when n' is an integer multiple of the true n
(n'=m*n reproduces a scaled hit r'~m*r -- an expected structural consequence,
tracked separately, not a false positive). This script asks whether a
public-computable score of n'*Q (or its best Apt-reduction over a small
k'-grid) separates n'=n from n'!=n, using ONLY (X, Y, bits) as inputs -- the
n-label is used ONLY to evaluate, never as a feature.

Two parts:
  (A) Positive control (MANDATORY): small-N (bands 16/20/24; N<=12 excluded
      because |D|=O(1) there by construction, making Q accidentally tiny for
      EVERY candidate n' and contaminating the wrong-n' bucket -- confirmed
      by direct inspection) EXACT hash-table brute force. Builds
      {point(r*G): r in [-R_MAX,R_MAX]}, R_MAX sized off the verified
      empirical |r| constant, and checks that the TRUE (n,k) yields an exact
      hit recovering r at a much higher rate than GENERIC (non-multiple)
      wrong n'.
  (B) Main statistical sweep, N in 8..120, <=200 keys/band, subsampled
      k'-grid (T_MAX) for the reduced score. Computes several public scores
      per (key, n'), then KS-tests {n'=n} vs {n'!=n} pooled over all keys,
      with Bonferroni correction over scores, a label-permutation null,
      and top-1%/top-10% ranking power of the true n by best score.

Run: python3 wp1_run.py
Writes RESULTS/WP1_nq_nearmiss.json
"""
from __future__ import annotations
import sys, os, json, time, math
import numpy as np
from scipy import stats

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lib_data as L
import lib_control as C

T0 = time.time()
RESULTS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "RESULTS")
OUT_PATH = os.path.join(RESULTS_DIR, "WP1_nq_nearmiss.json")

RNG_SEED = 20260706
BAND_LO, BAND_HI = 8, 120
KEYS_PER_BAND = 200
N_CANDIDATES = 256          # n' in 1..256
T_MAX = 3                   # k'-grid size for the reduced score (0..T_MAX-1)
# Small-N exact-match control. NOTE on the identity (verified numerically
# before this run, not assumed from the brief's literal wording): the exact
# small-DL perturbation is r = n*D - ((2^(N-1)*k) mod n) -- confirmed to
# satisfy n*Q - k*Apt == r*G as an EXACT point equality for every checked key.
# The brief's stated bound "|r| < 2^(N-1)/n" does NOT hold in general (checked
# N=16..32: |r| tracks ~2^(N-1)/256, i.e. a band-wide constant set by
# max_den=256, not shrinking with n; ~83% of keys satisfy |r|<2^(N-1)/256, the
# rest have a heavier tail). Hash-table radius below is sized empirically
# (16x that constant) for ~99% true-key coverage while keeping build times
# bounded. Bands 16/20/24 avoid the N<=12 degenerate regime where |D| is O(1)
# by construction (band width itself is only 2^11), which makes Q accidentally
# tiny for EVERY candidate n' and contaminates the wrong-n' control bucket --
# confirmed by direct inspection during development, not assumed.
SMALL_N_CONTROL_BANDS = [16, 20, 24]
CONTROL_RADIUS_MULT = 16    # hash-table radius = MULT * 2^(N-1)/256
CONTROL_KEYS_PER_BAND = 120  # small-N control: keys tested per band
CONTROL_NPRIME_SAMPLE = 40  # wrong-n' candidates sampled per key for control
CONTROL_KGRID = 64          # k'-grid depth used inside the control loop too

PMOD = L.P

# ------------------------------------------------------------------ scores --
def score_bundle(pt):
    """Public scores of an EC point (x,y). Returns a dict name->value.
    ATTACK-VALID: computed purely from the point's coordinates."""
    if pt is L.INF:
        # point at infinity -- degenerate; treat as maximally "small" is wrong,
        # give neutral / worst-case values so it doesn't masquerade as a hit
        return {
            "min_x": PMOD // 2, "min_y": PMOD // 2,
            "hw_x": 128, "hw_y": 128,
            "ent_x_lo32": 32.0,
            "x_mod3": 0, "x_mod5": 0, "x_mod7": 0, "x_mod11": 0, "x_mod13": 0,
        }
    x, y = pt
    min_x = min(x, PMOD - x)
    min_y = min(y, PMOD - y)
    hw_x = bin(x).count("1")
    hw_y = bin(y).count("1")
    lo32 = x & 0xFFFFFFFF
    ent_x_lo32 = shannon_entropy_bits(lo32, 32)
    return {
        "min_x": min_x, "min_y": min_y,
        "hw_x": hw_x, "hw_y": hw_y,
        "ent_x_lo32": ent_x_lo32,
        "x_mod3": x % 3, "x_mod5": x % 5, "x_mod7": x % 7,
        "x_mod11": x % 11, "x_mod13": x % 13,
    }


def shannon_entropy_bits(v: int, nbits: int) -> float:
    """Shannon entropy (bits) of the bit-symbol distribution of v's nbits,
    treated as a sequence of individual bits (0/1 alphabet). This is a cheap
    public "randomness" proxy: entropy of the empirical 0/1 frequency."""
    ones = bin(v).count("1")
    zeros = nbits - ones
    p1 = ones / nbits
    p0 = zeros / nbits
    e = 0.0
    for p in (p0, p1):
        if p > 0:
            e -= p * math.log2(p)
    return e * nbits  # scale to "bits of entropy" over the block


SCORE_NAMES_SMALLNESS = ["min_x", "min_y", "hw_x", "hw_y"]  # smaller = more "hit-like"
SCORE_NAMES_MOD = ["x_mod3", "x_mod5", "x_mod7", "x_mod11", "x_mod13"]  # ==0 = more "hit-like"
SCORE_NAMES_ENT = ["ent_x_lo32"]  # smaller = less random = more "hit-like"

ALL_SCORE_NAMES = SCORE_NAMES_SMALLNESS + SCORE_NAMES_MOD + SCORE_NAMES_ENT

# For ranking (best = smallest score meaning "most structured"), mod-residue
# scores need a distance-to-zero transform (residue r in [0,q) -> min(r,q-r)).
MOD_Q = {"x_mod3": 3, "x_mod5": 5, "x_mod7": 7, "x_mod11": 11, "x_mod13": 13}


def mod_dist(score_name, val):
    q = MOD_Q[score_name]
    return min(val, q - val)


# attack-valid guard: features are computed from (X,Y) coordinates of derived
# EC points only, never from d,n,k,D. Declare the public inputs used:
L.assert_attack_valid(["X", "Y", "bits"])


# -------------------------------------------------------- main sweep (B) ----
def run_band(df_band, N, rng):
    """Returns list of per-(key,n') score dict rows (as flat numpy arrays) plus
    per-key best-score-rank bookkeeping for the true n."""
    Apt = L.band_anchor(N)
    negApt = L.ec_neg(Apt)

    n_keys = len(df_band)
    # storage: for each score, array of shape (n_keys, N_CANDIDATES)
    direct_scores = {s: np.empty((n_keys, N_CANDIDATES), dtype=float) for s in ALL_SCORE_NAMES}
    reduced_scores = {s: np.empty((n_keys, N_CANDIDATES), dtype=float)
                       for s in (SCORE_NAMES_SMALLNESS[:2])}  # min_x/min_y only (cost)
    true_n_arr = np.empty(n_keys, dtype=int)

    for i, (_, r) in enumerate(df_band.iterrows()):
        P = (int(r.X), int(r.Y))
        true_n_arr[i] = int(r.n)
        Q = L.ec_add(P, L.ec_neg(Apt))
        # incremental j*Q for j=1..N_CANDIDATES
        jQ = [None] * (N_CANDIDATES + 1)
        cur = L.INF
        for j in range(1, N_CANDIDATES + 1):
            cur = L.ec_add(cur, Q)
            jQ[j] = cur

        for nprime in range(1, N_CANDIDATES + 1):
            Rpt = jQ[nprime]
            sb = score_bundle(Rpt)
            for s in ALL_SCORE_NAMES:
                direct_scores[s][i, nprime - 1] = sb[s]

            # reduced score: min over k'-grid of min(x,p-x)/min(y,p-y) of
            # R = n'*Q - k'*Apt, k' = 0..min(T_MAX,nprime)-1
            best_min_x = sb["min_x"]
            best_min_y = sb["min_y"]
            cur_r = Rpt
            for _k in range(1, min(T_MAX, nprime)):
                cur_r = L.ec_add(cur_r, negApt)
                if cur_r is L.INF:
                    continue
                x, y = cur_r
                mx = min(x, PMOD - x)
                my = min(y, PMOD - y)
                if mx < best_min_x:
                    best_min_x = mx
                if my < best_min_y:
                    best_min_y = my
            reduced_scores["min_x"][i, nprime - 1] = best_min_x
            reduced_scores["min_y"][i, nprime - 1] = best_min_y

    return direct_scores, reduced_scores, true_n_arr


def main():
    log = []
    def LOG(msg):
        elapsed = time.time() - T0
        line = f"[{elapsed:7.1f}s] {msg}"
        print(line, flush=True)
        log.append(line)

    result = {
        "wp": "WP1_nq_nearmiss",
        "model": "sonnet",
        "n_samples": None,
        "bit_range": [BAND_LO, BAND_HI],
        "attack_valid": True,
        "positive_control": {},
        "null_model": "wrong-n' candidates within key + label permutation within band",
        "primary_result": {},
        "reading": None,
        "artifacts": [],
        "runtime_sec": None,
        "params": {
            "keys_per_band": KEYS_PER_BAND,
            "n_candidates": N_CANDIDATES,
            "t_max_kgrid": T_MAX,
            "small_n_control_bands": SMALL_N_CONTROL_BANDS,
            "control_radius_mult": CONTROL_RADIUS_MULT,
            "control_keys_per_band": CONTROL_KEYS_PER_BAND,
            "control_nprime_sample": CONTROL_NPRIME_SAMPLE,
            "control_kgrid": CONTROL_KGRID,
        },
        "log": [],
    }

    try:
        LOG("loading dataset")
        df_full = L.load()
        rng = np.random.default_rng(RNG_SEED)

        # ============================================================
        # PART A: positive control -- small-N exact hash-table match
        # ============================================================
        LOG("=== positive control: small-N exact match ===")
        control_hits_true = 0
        control_trials_true = 0
        control_hits_wrong = 0
        control_trials_wrong = 0
        control_hits_wrong_nonmultiple = 0
        control_trials_wrong_nonmultiple = 0
        control_detail = []
        multiple_hit_detail = []

        for N in SMALL_N_CONTROL_BANDS:
            band = df_full[df_full.bits == N]
            if len(band) == 0:
                continue
            samp = band.sample(n=min(CONTROL_KEYS_PER_BAND, len(band)),
                                random_state=RNG_SEED + N)
            Apt = L.band_anchor(N)
            negApt = L.ec_neg(Apt)
            A = 1 << (N - 1)
            # empirically-sized radius (see params comment above): covers
            # ~99% of true keys' |r| = |n*D - (A*k mod n)| while staying fast.
            R_MAX = CONTROL_RADIUS_MULT * (A // 256)

            LOG(f"  N={N}: building hash table radius={R_MAX} "
                f"({len(samp)} keys sampled)")
            t_build0 = time.time()
            # table: point(x,y) -> r, for r = -R_MAX..R_MAX (x(rG)=x(-rG) but
            # y differs sign, so store full point to disambiguate)
            table = {L.INF: 0}
            pos = L.INF
            neg = L.INF
            for r in range(1, R_MAX + 1):
                pos = L.ec_add(pos, L.G)
                table[pos] = r
                neg = L.ec_add(neg, L.ec_neg(L.G))
                table[neg] = -r
            LOG(f"    table built: {len(table)} entries in {time.time()-t_build0:.1f}s")

            for _, row in samp.iterrows():
                P = (int(row.X), int(row.Y))
                true_n, true_k, true_D = int(row.n), int(row.k), int(row.D)
                Q = L.ec_add(P, L.ec_neg(Apt))

                # candidate n' pool: true n plus a random sample of wrong n'
                wrong_pool = [x for x in range(1, N_CANDIDATES + 1) if x != true_n]
                wrong_sample = list(rng.choice(wrong_pool,
                                                size=min(CONTROL_NPRIME_SAMPLE, len(wrong_pool)),
                                                replace=False))
                test_nprimes = [true_n] + wrong_sample

                # incremental jQ
                jQ = [None] * (N_CANDIDATES + 1)
                cur_q = L.INF
                for j in range(1, N_CANDIDATES + 1):
                    cur_q = L.ec_add(cur_q, Q)
                    jQ[j] = cur_q

                for nprime in test_nprimes:
                    is_true = (nprime == true_n)
                    is_multiple = (not is_true) and (nprime % true_n == 0)
                    Rj = jQ[nprime]
                    hit = False
                    hit_r = None
                    hit_k = None
                    cur_r = Rj
                    kbound = min(nprime, CONTROL_KGRID)
                    for kprime in range(0, kbound):
                        if kprime > 0:
                            cur_r = L.ec_add(cur_r, negApt)
                        if cur_r in table:
                            hit = True
                            hit_r = table[cur_r]
                            hit_k = kprime
                            break
                    if is_true:
                        control_trials_true += 1
                        control_hits_true += int(hit)
                        if hit:
                            control_detail.append({
                                "N": N, "true_n": true_n, "true_k": true_k,
                                "recovered_r": hit_r, "recovered_kprime": hit_k,
                            })
                    else:
                        control_trials_wrong += 1
                        control_hits_wrong += int(hit)
                        if not is_multiple:
                            control_trials_wrong_nonmultiple += 1
                            control_hits_wrong_nonmultiple += int(hit)
                        elif hit:
                            # structural artifact: nprime = m*true_n implies
                            # nprime*Q = m*(true_n*Q) = m*k*Apt + m*r*G, so a
                            # small hit at kp=m*true_k with recovered_r ~ m*r
                            # is EXPECTED, not a false positive of the method.
                            multiple_hit_detail.append({
                                "N": N, "true_n": true_n, "nprime": nprime,
                                "multiple": nprime // true_n,
                                "recovered_r": hit_r,
                            })

            LOG(f"  N={N} done (cumulative): true hits {control_hits_true}/{control_trials_true}, "
                f"wrong hits {control_hits_wrong}/{control_trials_wrong}, "
                f"wrong-nonmultiple hits {control_hits_wrong_nonmultiple}/"
                f"{control_trials_wrong_nonmultiple}")

        hit_rate_true = control_hits_true / control_trials_true if control_trials_true else 0.0
        hit_rate_wrong = control_hits_wrong / control_trials_wrong if control_trials_wrong else 0.0
        hit_rate_wrong_nonmult = (control_hits_wrong_nonmultiple / control_trials_wrong_nonmultiple
                                   if control_trials_wrong_nonmultiple else 0.0)

        def prop_z(h1, n1, h2, n2):
            if n1 == 0 or n2 == 0:
                return None
            p1, p2 = h1 / n1, h2 / n2
            p_pool = (h1 + h2) / (n1 + n2)
            se = math.sqrt(p_pool * (1 - p_pool) * (1 / n1 + 1 / n2)) if 0 < p_pool < 1 else 0.0
            if se > 0:
                return (p1 - p2) / se
            return float("inf") if p1 > p2 else 0.0

        control_z = prop_z(control_hits_true, control_trials_true,
                            control_hits_wrong, control_trials_wrong)
        control_z_nonmult = prop_z(control_hits_true, control_trials_true,
                                    control_hits_wrong_nonmultiple, control_trials_wrong_nonmultiple)

        # Detection is judged against the GENERIC (non-multiple) wrong-n'
        # bucket -- the multiple-of-n bucket is expected to hit structurally
        # (see docstring) and would inflate hit_rate_wrong without reflecting
        # detector power against a truly wrong candidate.
        control_detected = (control_z_nonmult is not None and control_z_nonmult >= 5) or \
                            (hit_rate_wrong_nonmult == 0.0 and control_hits_true > 0 and
                             control_trials_true >= 10)

        LOG(f"positive control: true hit-rate={hit_rate_true:.4f} "
            f"({control_hits_true}/{control_trials_true}), "
            f"wrong hit-rate={hit_rate_wrong:.6f} "
            f"({control_hits_wrong}/{control_trials_wrong}), "
            f"wrong-nonmultiple hit-rate={hit_rate_wrong_nonmult:.6f} "
            f"({control_hits_wrong_nonmultiple}/{control_trials_wrong_nonmultiple}), "
            f"z={control_z}, z_nonmult={control_z_nonmult}, detected={control_detected}")
        LOG(f"  multiple-of-true-n structural hits: {len(multiple_hit_detail)} "
            f"(expected artifact: nprime=m*n gives recovered_r ~ m*r_true, not a "
            f"false positive -- see identity derivation)")

        result["positive_control"] = {
            "method": "exact hash-table brute force of {point(r*G): r in "
                      "[-R_MAX, R_MAX]}, R_MAX = "
                      f"{CONTROL_RADIUS_MULT}*2^(N-1)/256 per band (empirically "
                      "sized for ~99% true-key coverage; see params comment for "
                      "the corrected r = n*D - (2^(N-1)*k mod n) identity used, "
                      "which differs from the brief's literal |r|<2^(N-1)/n).",
            "bands_tested": SMALL_N_CONTROL_BANDS,
            "keys_per_band": CONTROL_KEYS_PER_BAND,
            "wrong_nprime_sampled_per_key": CONTROL_NPRIME_SAMPLE,
            "kgrid_depth": CONTROL_KGRID,
            "true_hit_rate": hit_rate_true,
            "true_hits": control_hits_true,
            "true_trials": control_trials_true,
            "wrong_hit_rate": hit_rate_wrong,
            "wrong_hits": control_hits_wrong,
            "wrong_trials": control_trials_wrong,
            "wrong_nonmultiple_hit_rate": hit_rate_wrong_nonmult,
            "wrong_nonmultiple_hits": control_hits_wrong_nonmultiple,
            "wrong_nonmultiple_trials": control_trials_wrong_nonmultiple,
            "control_z": control_z,
            "control_z_nonmultiple": control_z_nonmult,
            "detected": control_detected,
            "example_recoveries": control_detail[:10],
            "note_multiple_of_n_artifact": (
                "wrong n'=m*true_n structurally reproduces a scaled hit "
                "(recovered_r ~ m*r_true) because n'*Q = m*(n*Q) = m*k*Apt + "
                "m*r*G -- this is an expected consequence of the identity, not "
                "a false positive of the detector. Excluded from "
                "wrong_nonmultiple_* to isolate the detector's power against "
                "generic (non-multiple) wrong n'."
            ),
            "multiple_of_n_hits_observed": len(multiple_hit_detail),
            "multiple_of_n_examples": multiple_hit_detail[:10],
        }

        if not control_detected:
            LOG("POSITIVE CONTROL DID NOT FIRE -- per protocol, result is "
                "INCONCLUSIVE (underpowered), not a negative.")

        # ============================================================
        # PART B: main statistical sweep, N in 8..120
        # ============================================================
        LOG("=== main sweep: N in 8..120 ===")
        bands = sorted(df_full[(df_full.bits >= BAND_LO) & (df_full.bits <= BAND_HI)]
                        .bits.unique().tolist())
        LOG(f"{len(bands)} bands to process")

        # pooled accumulators across all bands: for each score, list of
        # (is_true, value) -- but pooling raw values across bands with very
        # different magnitudes (min_x, min_y depend on ~2^256 range regardless
        # of N since P is fixed secp256k1 field) is fine for min_x/min_y/entropy
        # (field-size scores, N-independent range); hw_x/hw_y are ~Binomial(256,.5)
        # regardless of N too. mod-residues are always small. So pooling across
        # bands is apples-to-apples.
        pooled_true = {s: [] for s in ALL_SCORE_NAMES}
        pooled_wrong = {s: [] for s in ALL_SCORE_NAMES}
        pooled_true_reduced = {s: [] for s in reduced_scores_keys()}
        pooled_wrong_reduced = {s: [] for s in reduced_scores_keys()}

        # permutation-null accumulators (per band, permute which n' is "true")
        perm_true = {s: [] for s in ALL_SCORE_NAMES}
        perm_wrong = {s: [] for s in ALL_SCORE_NAMES}

        # ranking power bookkeeping
        rank_frac_top1 = {s: 0 for s in ALL_SCORE_NAMES}
        rank_frac_top10 = {s: 0 for s in ALL_SCORE_NAMES}
        rank_frac_top1_red = {s: 0 for s in reduced_scores_keys()}
        rank_frac_top10_red = {s: 0 for s in reduced_scores_keys()}
        n_keys_total = 0

        for bi, N in enumerate(bands):
            band = df_full[df_full.bits == N]
            samp = band.sample(n=min(KEYS_PER_BAND, len(band)), random_state=RNG_SEED + N)
            n_keys = len(samp)
            n_keys_total += n_keys

            direct_scores, reduced, true_n_arr = run_band(samp, N, rng)

            # ---- pooled true/wrong split (direct scores) ----
            for s in ALL_SCORE_NAMES:
                arr = direct_scores[s]  # (n_keys, 256)
                for i in range(n_keys):
                    tn = true_n_arr[i]
                    row = arr[i]
                    pooled_true[s].append(row[tn - 1])
                    # subsample wrong n' to keep pooled arrays bounded: take all
                    # (256-1 per key is fine, arrays stay manageable: ~22.5k*255)
                    mask = np.ones(N_CANDIDATES, dtype=bool)
                    mask[tn - 1] = False
                    pooled_wrong[s].extend(row[mask].tolist())

            for s in reduced_scores_keys():
                arr = reduced[s]
                for i in range(n_keys):
                    tn = true_n_arr[i]
                    row = arr[i]
                    pooled_true_reduced[s].append(row[tn - 1])
                    mask = np.ones(N_CANDIDATES, dtype=bool)
                    mask[tn - 1] = False
                    pooled_wrong_reduced[s].extend(row[mask].tolist())

            # ---- label permutation null (within band) ----
            perm_n_arr = rng.permutation(true_n_arr)
            for s in ALL_SCORE_NAMES:
                arr = direct_scores[s]
                for i in range(n_keys):
                    pn = perm_n_arr[i]
                    row = arr[i]
                    perm_true[s].append(row[pn - 1])
                    mask = np.ones(N_CANDIDATES, dtype=bool)
                    mask[pn - 1] = False
                    perm_wrong[s].extend(row[mask].tolist())

            # ---- ranking power: is true-n in top1%/top10% by best score? ----
            top1_n = max(1, round(N_CANDIDATES * 0.01))
            top10_n = max(1, round(N_CANDIDATES * 0.10))
            for s in ALL_SCORE_NAMES:
                arr = direct_scores[s]
                for i in range(n_keys):
                    tn = true_n_arr[i]
                    row = arr[i]
                    if s in MOD_Q:
                        dvals = np.minimum(row, MOD_Q[s] - row)
                        order = np.argsort(dvals)  # smallest distance-to-0 = best
                    else:
                        order = np.argsort(row)  # smaller = more "hit-like"
                    rank_of_true = int(np.where(order == (tn - 1))[0][0])
                    if rank_of_true < top1_n:
                        rank_frac_top1[s] += 1
                    if rank_of_true < top10_n:
                        rank_frac_top10[s] += 1
            for s in reduced_scores_keys():
                arr = reduced[s]
                for i in range(n_keys):
                    tn = true_n_arr[i]
                    row = arr[i]
                    order = np.argsort(row)
                    rank_of_true = int(np.where(order == (tn - 1))[0][0])
                    if rank_of_true < top1_n:
                        rank_frac_top1_red[s] += 1
                    if rank_of_true < top10_n:
                        rank_frac_top10_red[s] += 1

            if (bi + 1) % 10 == 0 or bi == len(bands) - 1:
                LOG(f"  band {bi+1}/{len(bands)} (N={N}, {n_keys} keys) done, "
                    f"cumulative keys={n_keys_total}")

        LOG(f"main sweep done: {n_keys_total} keys total across {len(bands)} bands")

        # ============================================================
        # KS tests: pooled true vs wrong, per score, Bonferroni over scores
        # ============================================================
        LOG("computing KS tests")
        n_score_tests = len(ALL_SCORE_NAMES) + len(reduced_scores_keys())
        ks_results = {}
        for s in ALL_SCORE_NAMES:
            t_arr = np.array(pooled_true[s], dtype=float)
            w_arr = np.array(pooled_wrong[s], dtype=float)
            ks_stat, ks_p = stats.ks_2samp(t_arr, w_arr)
            ks_results[s] = {
                "ks_stat": float(ks_stat),
                "p_raw": float(ks_p),
                "p_bonferroni": float(min(1.0, ks_p * n_score_tests)),
                "n_true": int(len(t_arr)),
                "n_wrong": int(len(w_arr)),
                "mean_true": float(t_arr.mean()),
                "mean_wrong": float(w_arr.mean()),
            }
        for s in reduced_scores_keys():
            t_arr = np.array(pooled_true_reduced[s], dtype=float)
            w_arr = np.array(pooled_wrong_reduced[s], dtype=float)
            ks_stat, ks_p = stats.ks_2samp(t_arr, w_arr)
            ks_results[f"reduced_{s}"] = {
                "ks_stat": float(ks_stat),
                "p_raw": float(ks_p),
                "p_bonferroni": float(min(1.0, ks_p * n_score_tests)),
                "n_true": int(len(t_arr)),
                "n_wrong": int(len(w_arr)),
                "mean_true": float(t_arr.mean()),
                "mean_wrong": float(w_arr.mean()),
            }

        # permutation-null KS (label permuted within band) -- sanity: should
        # show NO separation (this validates the KS machinery itself, since a
        # permuted label is definitionally null)
        perm_ks_results = {}
        for s in ALL_SCORE_NAMES:
            t_arr = np.array(perm_true[s], dtype=float)
            w_arr = np.array(perm_wrong[s], dtype=float)
            ks_stat, ks_p = stats.ks_2samp(t_arr, w_arr)
            perm_ks_results[s] = {"ks_stat": float(ks_stat), "p_raw": float(ks_p)}

        any_significant = any(v["p_bonferroni"] < 0.05 for v in ks_results.values())
        LOG(f"KS tests done. any score significant after Bonferroni: {any_significant}")
        for s, v in ks_results.items():
            LOG(f"  {s}: KS={v['ks_stat']:.5f} p_bonf={v['p_bonferroni']:.3g} "
                f"mean_true={v['mean_true']:.4g} mean_wrong={v['mean_wrong']:.4g}")

        # ranking power fractions
        ranking_power = {
            s: {
                "top1pct_frac": rank_frac_top1[s] / n_keys_total,
                "top10pct_frac": rank_frac_top10[s] / n_keys_total,
            } for s in ALL_SCORE_NAMES
        }
        for s in reduced_scores_keys():
            ranking_power[f"reduced_{s}"] = {
                "top1pct_frac": rank_frac_top1_red[s] / n_keys_total,
                "top10pct_frac": rank_frac_top10_red[s] / n_keys_total,
            }
        expected_top1_baseline = 0.01
        expected_top10_baseline = 0.10
        LOG("ranking power (top1%/top10% true-n hit-rate vs baseline "
            f"{expected_top1_baseline}/{expected_top10_baseline}):")
        for s, v in ranking_power.items():
            LOG(f"  {s}: top1%={v['top1pct_frac']:.4f} top10%={v['top10pct_frac']:.4f}")

        result["n_samples"] = n_keys_total
        result["primary_result"] = {
            "ks_tests": ks_results,
            "permutation_null_ks": perm_ks_results,
            "n_score_tests_bonferroni": n_score_tests,
            "any_score_significant_after_bonferroni": any_significant,
            "ranking_power": ranking_power,
            "ranking_baseline": {
                "top1pct": expected_top1_baseline,
                "top10pct": expected_top10_baseline,
            },
        }

        # ============================================================
        # reading (conditional, bounded)
        # ============================================================
        if not control_detected:
            reading = ("INCONCLUSIVE -- positive control did not fire; test "
                       "underpowered, large-N statistical result not reported "
                       "as a negative or a positive.")
        else:
            best_score = max(ks_results.items(), key=lambda kv: kv[1]["ks_stat"])
            if any_significant:
                reading = (
                    f"CONDITIONAL POSITIVE (bounded): with positive control firing "
                    f"(true hit-rate {hit_rate_true:.3f} vs generic-wrong "
                    f"{hit_rate_wrong_nonmult:.4g}, z={control_z_nonmult}), the small-N "
                    f"exact identity is confirmed real. At N in [{BAND_LO},{BAND_HI}] "
                    f"with {KEYS_PER_BAND} keys/band, k'-grid depth {T_MAX}, and "
                    f"{n_score_tests} scores tested, score '{best_score[0]}' shows "
                    f"KS={best_score[1]['ks_stat']:.4g} (Bonferroni "
                    f"p={best_score[1]['p_bonferroni']:.3g}) separating n'=n from "
                    f"n'!=n. Ranking payoff: top1%/top10% hit-rates listed in "
                    f"ranking_power, vs baselines {expected_top1_baseline}/"
                    f"{expected_top10_baseline}. This is a posterior shift on n, "
                    f"not recovery of d."
                )
            else:
                reading = (
                    f"CONDITIONAL NEGATIVE (bounded): positive control fired "
                    f"(true hit-rate {hit_rate_true:.3f} vs generic-wrong "
                    f"{hit_rate_wrong_nonmult:.4g}, z={control_z_nonmult}; note a "
                    f"separate, expected structural effect at n'=multiples-of-true-n "
                    f"raises the pooled wrong-hit-rate to {hit_rate_wrong:.4g} -- see "
                    f"note_multiple_of_n_artifact), confirming the identity is real "
                    f"and detectable when |r| is small enough to brute force (bands "
                    f"{SMALL_N_CONTROL_BANDS}). At N in [{BAND_LO},{BAND_HI}] "
                    f"({n_keys_total} keys, {KEYS_PER_BAND} keys/band cap, k'-grid "
                    f"depth {T_MAX}, {n_score_tests} scores with Bonferroni "
                    f"correction), no score showed significant n'=n vs n'!=n "
                    f"separation. This is bounded to this feature set, this sample "
                    f"size, this k'-grid depth, and this N-range -- not a claim that "
                    f"no public statistic ever separates true n at these "
                    f"bit-lengths (the perturbation r's typical magnitude tracks "
                    f"2^(N-1)/256 regardless of n, so at large N a fixed small "
                    f"k'-grid and these coarse scores are expected to lose power "
                    f"relative to a full brute-force radius; a real DL-distance "
                    f"oracle or deeper k'-grid was not run here, per the runtime "
                    f"budget)."
                )
        result["reading"] = reading
        LOG("READING: " + reading)

    except Exception as e:
        import traceback
        tb = traceback.format_exc()
        LOG(f"EXCEPTION: {e}\n{tb}")
        result["reading"] = (f"BLOCKED / PARTIAL -- exception during run: {e}. "
                             f"Partial results (if any) reflect progress up to failure.")
        result["error"] = str(e)
        result["traceback"] = tb

    result["runtime_sec"] = time.time() - T0
    result["log"] = log

    os.makedirs(RESULTS_DIR, exist_ok=True)
    with open(OUT_PATH, "w") as f:
        json.dump(result, f, indent=2, default=str)
    LOG(f"wrote {OUT_PATH}")
    return result


def reduced_scores_keys():
    return ["min_x", "min_y"]


if __name__ == "__main__":
    main()
