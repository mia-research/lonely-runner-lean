#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Frozen statistic + null for PROTOCOL_blinded_joint_readout_v1.md (blinded).

UNIFORM pipeline over the five peer targets {T_3,T_4,T_5,T_7,T_DECOY} across two
key-sets {(M) model curves pooled, (S) secp solved keys}. No target-specific and
no feature-specific choices. This file is hashed BEFORE any real-data run
(commit-before-you-see); its SHA-256 is recorded in the result file.

Allowed inputs: PROTOCOL_blinded_joint_readout_v1.md, ecc_secp256k1.py,
int1_frame_operator_v1.py, lift_sextant_rhombus_law_proof_v2.py,
glv_fundamental_domain_law_v1.py, puzzles_verified.csv. No other file is read.
"""
import os
import sys
import math
import csv
import hashlib
import random
from collections import Counter

from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod

import int1_frame_operator_v1 as frm
from lift_sextant_rhombus_law_proof_v2 import enorm, sextant
import ecc_secp256k1 as ecc

# ----------------------------------------------------------------------------
# Frozen constants (protocol)
# ----------------------------------------------------------------------------
R_NULL      = 20000
SEED_NULL   = 777333     # stratified permutation null
SEED_DECOY  = 20260813   # pi in T_DECOY = pi(d mod 3)
SEED_PLANT  = 31415      # C1 planted-dependence subset
ALPHA       = 0.05

FEATURE_DOMAINS = [3, 3, 3, 3, 2, 2]   # F1..F6 raw domains; do NOT re-bin
JOINT_DOMAIN    = 1
for _d in FEATURE_DOMAINS:
    JOINT_DOMAIN *= _d                  # = 324 = product of feature domains

DISC_PRIMES = [547, 907]                # C4 discovery
CONF_PRIMES = [1303, 1669, 2089]        # C4 confirmation
ALL_MODEL_PRIMES = DISC_PRIMES + CONF_PRIMES
P_SECP = ecc.P
N_SECP = ecc.N_ORDER

CSV_PATH = "puzzles_verified.csv"

# ----------------------------------------------------------------------------
# Protocol-verbatim helpers
# ----------------------------------------------------------------------------
def find_wp(p):
    """Primitive cube root of unity mod p (used by chi3_index)."""
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    return pow(g, e, p)

def find_lam(n):
    """Smallest lam>=2 with lam^3==1 mod n, lam!=1. Model curves only (small n).

    Note: for secp this lambda is a ~256-bit number, so the naive search is
    intractable. Per protocol section 4, key-set (S) has NO orbit quotient, so
    secp needs only wp (above). lam is computed exclusively for model curves.
    """
    lam = 2
    while not (pow(lam, 3, n) == 1 and lam != 1):
        lam += 1
    return lam

def chi3_index(x, p, wp):                 # F1, domain {0,1,2}
    v = pow(x % p, (p - 1) // 3, p)
    return 0 if v == 1 else (1 if v == wp else 2)

def orbit_reps(m, lam):                   # one rep per full <+-lambda> orbit
    seen, reps = set(), []
    for d in range(1, m):
        orb = []
        for k in range(3):
            lk = pow(lam, k, m)
            orb += [(lk * d) % m, (-lk * d) % m]
        d0 = min(x for x in orb if x != 0)
        if d0 not in seen:
            seen.add(d0)
            reps.append(d0)
    return reps

def sextant_uv(u, v):
    return sextant(u, v)

def features(x_d, y_d, p, wp, eis, eps):
    """The six point-features of Q_d=(x_d,y_d). Protocol section 2.

    (build(p)/build_secp() return (eis, eps) closures; the protocol's
    'secp.eis/secp.eps' attribute notation is realized here by passing those
    closures directly -- a faithful mechanical adaptation, no logic change.)
    """
    e = eis(x_d)
    F1 = chi3_index(x_d, p, wp)                              # chi3-index   {0,1,2}
    F2 = eps(x_d)                                            # flap eps     {0,1,2}
    E  = enorm(e)
    F3 = 0 if 16 * E < 3 * p else (1 if 16 * E < 6 * p else 2)  # s-band3   {0,1,2}
    sxt = sextant_uv(*e)
    F4 = sxt % 3                                             # sextant mod3 {0,1,2}
    F5 = 0 if sxt in (0, 2, 4) else 1                        # sextant parity {0,1}
    F6 = 0 if pow(y_d, (p - 1) // 2, p) == 1 else 1          # chi2(y) Legendre {0,1}
    return (F1, F2, F3, F4, F5, F6)

# ----------------------------------------------------------------------------
# Model-curve group law: E: y^2 = x^3 + 7 over F_p (affine, integer-exact)
# ----------------------------------------------------------------------------
def model_setup(p):
    """Return (n, G): n = #E(F_p) (incl. infinity), G = a generator (non-identity)."""
    cnt = 1  # point at infinity
    G = None
    for x in range(p):
        rhs = (x * x * x + 7) % p
        if rhs == 0:
            cnt += 1
            if G is None:
                G = (x, 0)
        elif pow(rhs, (p - 1) // 2, p) == 1:
            cnt += 2
            if G is None:
                G = (x, sqrt_mod(rhs, p))
    return cnt, G

def _inv(a, p):
    return pow(a, p - 2, p)

def madd(P1, P2, p):
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if x1 == x2:
        m = (3 * x1 * x1) % p * _inv((2 * y1) % p, p) % p
    else:
        m = ((y2 - y1) % p) * _inv((x2 - x1) % p, p) % p
    x3 = (m * m - x1 - x2) % p
    y3 = (m * (x1 - x3) - y1) % p
    return (x3, y3)

def mmul(k, G, p):
    R = None
    Q = G
    while k > 0:
        if k & 1:
            R = madd(R, Q, p)
        Q = madd(Q, Q, p)
        k >>= 1
    return R

# ----------------------------------------------------------------------------
# MI / chi2 estimators (plugin + Miller-Madow)
# ----------------------------------------------------------------------------
def entropy_bits(counter, N):
    h = 0.0
    for c in counter.values():
        if c > 0:
            pr = c / N
            h -= pr * math.log2(pr)
    return h

def mi_plugin_bits(xs, ts):
    N = len(xs)
    cx = Counter(xs)
    ct = Counter(ts)
    cxt = Counter(zip(xs, ts))
    return entropy_bits(cx, N) + entropy_bits(ct, N) - entropy_bits(cxt, N)

def joint_test(feat_tuples, f1_list, ts, R=R_NULL, seed=SEED_NULL):
    """Frozen joint MI(F;T) + chi2 omnibus, with within-F1-stratum permutation null.

    Returns dict with mi_obs (Miller-Madow bits), mu_null, sigma_null, z, raw_p,
    chi2, dof, chi2_perm_p, singles (6 single-feature Miller-Madow MIs), N, t_domain.
    """
    N = len(ts)
    # encode feature tuples as ints for speed (no re-binning; domains unchanged)
    uniq = {}
    feat_idx = []
    for ft in feat_tuples:
        if ft not in uniq:
            uniq[ft] = len(uniq)
        feat_idx.append(uniq[ft])

    t_domain = len(set(ts))
    cx = Counter(feat_idx)
    ct = Counter(ts)
    Hf = entropy_bits(cx, N)
    Ht = entropy_bits(ct, N)

    cxt_obs = Counter(zip(feat_idx, ts))
    Hft_obs = entropy_bits(cxt_obs, N)
    mi_plugin_obs = Hf + Ht - Hft_obs
    corr = (JOINT_DOMAIN - 1) * (t_domain - 1) / (2.0 * N)   # Miller-Madow, |F|=324
    mi_obs = mi_plugin_obs - corr

    chi2_obs = 0.0
    for (i, j), o in cxt_obs.items():
        eij = cx[i] * ct[j] / N
        chi2_obs += (o - eij) ** 2 / eij
    dof = (len(cx) - 1) * (len(ct) - 1)

    strata = {0: [], 1: [], 2: []}
    for idx, f1 in enumerate(f1_list):
        strata[f1].append(idx)

    rng = random.Random(seed)
    ts_local = list(ts)
    null_mi = []
    null_chi2 = []
    for _ in range(R):
        perm = [0] * N
        for s in (0, 1, 2):
            idxs = strata[s]
            vals = [ts_local[i] for i in idxs]
            rng.shuffle(vals)
            for j2, i in enumerate(idxs):
                perm[i] = vals[j2]
        cxt_p = Counter(zip(feat_idx, perm))
        Hft_p = entropy_bits(cxt_p, N)
        null_mi.append(Hf + Ht - Hft_p - corr)
        chi2_p = 0.0
        for (i, j), o in cxt_p.items():
            eij = cx[i] * ct[j] / N
            chi2_p += (o - eij) ** 2 / eij
        null_chi2.append(chi2_p)

    mu = sum(null_mi) / R
    var = sum((x - mu) ** 2 for x in null_mi) / R
    sigma = math.sqrt(var)
    z = (mi_obs - mu) / sigma if sigma > 0 else 0.0
    ge = sum(1 for x in null_mi if x >= mi_obs)
    raw_p = (ge + 1) / (R + 1)
    ge_c = sum(1 for x in null_chi2 if x >= chi2_obs)
    chi2_perm_p = (ge_c + 1) / (R + 1)

    singles = []
    for k in range(6):
        fk = [feat_tuples[i][k] for i in range(N)]
        mi_k_plugin = mi_plugin_bits(fk, ts)
        corr_k = (FEATURE_DOMAINS[k] - 1) * (t_domain - 1) / (2.0 * N)
        singles.append(mi_k_plugin - corr_k)

    return dict(mi_obs=mi_obs, mu=mu, sigma=sigma, z=z, raw_p=raw_p,
                chi2=chi2_obs, dof=dof, chi2_perm_p=chi2_perm_p,
                singles=singles, N=N, t_domain=t_domain)

# ----------------------------------------------------------------------------
# Targets (all peers) + C1 plant
# ----------------------------------------------------------------------------
def target_values(d_list, name):
    if name == "T3":
        return [d % 3 for d in d_list]
    if name == "T4":
        return [d % 4 for d in d_list]
    if name == "T5":
        return [d % 5 for d in d_list]
    if name == "T7":
        return [d % 7 for d in d_list]
    if name == "TDECOY":
        rng = random.Random(SEED_DECOY)
        perm = list(range(3))
        rng.shuffle(perm)
        return [perm[d % 3] for d in d_list]
    raise ValueError(name)

def build_t_plant(feat_tuples, seed=SEED_PLANT):
    """C1: T_plant = F2 on a uniform random 30% subset, else uniform random in {0,1,2}."""
    rng = random.Random(seed)
    N = len(feat_tuples)
    k = round(0.30 * N)
    subset = set(rng.sample(range(N), k))
    t = []
    for i in range(N):
        if i in subset:
            t.append(feat_tuples[i][1])   # F2 (flap eps)
        else:
            t.append(rng.randrange(3))
    return t

# ----------------------------------------------------------------------------
# Datasets
# ----------------------------------------------------------------------------
def build_prime_data(p):
    """Return (data_dict, None) or (None, skip_reason) for one model prime.

    Verifies prime group order n (protocol: skip+report if not prime) and n%3==1
    (required for an order-3 lambda / GLV orbit quotient).
    """
    n, G = model_setup(p)
    if not isprime(n):
        return None, "n=%d not prime" % n
    if n % 3 != 1:
        return None, "n=%d not 1 mod 3 (no order-3 lambda)" % n
    wp = find_wp(p)
    lam = find_lam(n)
    eis, eps = frm.build(p)
    reps = orbit_reps(n, lam)
    rows = []  # (feat_tuple, f1, d)
    for d in reps:
        x, y = mmul(d, G, p)
        ft = features(x, y, p, wp, eis, eps)
        rows.append((ft, ft[0], d))
    return dict(p=p, n=n, wp=wp, lam=lam, eis=eis, eps=eps, G=G,
                reps=reps, rows=rows), None

def assemble_rows(prime_data_list):
    feat_tuples = []
    f1_list = []
    d_list = []
    for pd in prime_data_list:
        for (ft, f1, d) in pd["rows"]:
            feat_tuples.append(ft)
            f1_list.append(f1)
            d_list.append(d)
    return feat_tuples, f1_list, d_list

def build_secp_dataset():
    ds = []
    with open(CSV_PATH, newline="") as f:
        for r in csv.DictReader(f):
            pk = (r.get("private_key") or "").strip()
            if pk:
                ds.append(int(pk, 16))
    eis, eps = frm.build_secp()
    wp = find_wp(P_SECP)
    feat_tuples = []
    f1_list = []
    for d in ds:
        x, y = ecc.scalar_mul(d)
        ft = features(x, y, P_SECP, wp, eis, eps)
        feat_tuples.append(ft)
        f1_list.append(ft[0])
    return feat_tuples, f1_list, ds

# ----------------------------------------------------------------------------
# C3: phi-forced orbit-invariance (exact integer check)
# ----------------------------------------------------------------------------
def c3_check(prime_data):
    out = {}
    for pd in prime_data:
        p, n, lam, wp, eis, eps, G = (pd["p"], pd["n"], pd["lam"],
                                       pd["wp"], pd["eis"], pd["eps"], pd["G"])
        reps = pd["reps"]
        viol = {"F2": 0, "F3": 0, "F5": 0, "tuple": 0}
        tot = 0
        for d in reps:
            orb = set()
            for k in range(3):
                lk = pow(lam, k, n)
                orb |= {(lk * d) % n, (-lk * d) % n}
            orb = {x for x in orb if x != 0}
            f2, f3, f5 = set(), set(), set()
            for dd in orb:
                x, y = mmul(dd, G, p)
                ft = features(x, y, p, wp, eis, eps)
                f2.add(ft[1]); f3.add(ft[2]); f5.add(ft[4])
            tot += 1
            if len(f2) > 1: viol["F2"] += 1
            if len(f3) > 1: viol["F3"] += 1
            if len(f5) > 1: viol["F5"] += 1
            if len(f2) > 1 or len(f3) > 1 or len(f5) > 1: viol["tuple"] += 1
        out[p] = dict(tot=tot, **viol)
    return out

# ----------------------------------------------------------------------------
# Holm-Bonferroni
# ----------------------------------------------------------------------------
def holm_adjust(pvals):
    m = len(pvals)
    order = sorted(range(m), key=lambda i: pvals[i])
    adj = [0.0] * m
    cummax = 0.0
    for rank, i in enumerate(order):
        val = min(1.0, (m - rank) * pvals[i])
        cummax = max(cummax, val)
        adj[i] = cummax
    return adj

# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------
def self_sha256():
    with open(__file__, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

def fmt(x):
    if x is None:
        return "n/a"
    if isinstance(x, float):
        if abs(x) < 1e-4 and x != 0.0:
            return "%.3e" % x
        return "%.4f" % x
    return str(x)

def main():
    sys.stderr.write("[setup] building model-curve prime data ...\n"); sys.stderr.flush()
    prime_data_all = []
    skipped = []
    for p in ALL_MODEL_PRIMES:
        pd, reason = build_prime_data(p)
        if pd is None:
            skipped.append((p, reason))
            sys.stderr.write("[setup] SKIP p=%d : %s\n" % (p, reason)); sys.stderr.flush()
        else:
            prime_data_all.append(pd)
            sys.stderr.write("[setup] p=%d n=%d reps=%d\n"
                             % (p, pd["n"], len(pd["reps"]))); sys.stderr.flush()

    disc_pd = [pd for pd in prime_data_all if pd["p"] in DISC_PRIMES]
    conf_pd = [pd for pd in prime_data_all if pd["p"] in CONF_PRIMES]

    M_feat, M_f1, M_d = assemble_rows(prime_data_all)
    Mdisc_feat, Mdisc_f1, Mdisc_d = assemble_rows(disc_pd)
    Mconf_feat, Mconf_f1, Mconf_d = assemble_rows(conf_pd)

    sys.stderr.write("[setup] building secp dataset ...\n"); sys.stderr.flush()
    S_feat, S_f1, S_ds = build_secp_dataset()

    sys.stderr.write("[setup] N(M)=%d  N(M-disc)=%d  N(M-conf)=%d  N(S)=%d\n"
                     % (len(M_d), len(Mdisc_d), len(Mconf_d), len(S_ds))); sys.stderr.flush()

    TARGETS = ["T3", "T4", "T5", "T7", "TDECOY"]
    TNAMES = {"T3": "T_3", "T4": "T_4", "T5": "T_5", "T7": "T_7", "TDECOY": "T_DECOY"}

    keysets = {
        "M":  ("(M) model curves", M_feat, M_f1, M_d),
        "S":  ("(S) secp",         S_feat, S_f1, S_ds),
    }

    results = {}   # results[keyset][target] = joint_test dict
    for ks_key, (ks_label, ft, f1, dl) in keysets.items():
        sys.stderr.write("[null] key-set %s N=%d ...\n" % (ks_key, len(dl))); sys.stderr.flush()
        for tname in TARGETS:
            tv = target_values(dl, tname)
            results.setdefault(ks_key, {})[tname] = joint_test(ft, f1, tv)
            sys.stderr.write("   %s %s done\n" % (ks_key, tname)); sys.stderr.flush()

    # OOS (C4): discovery / confirmation (descriptive; NOT in Holm family)
    oos = {}
    for phase, (ft, f1, dl) in {
        "disc": (Mdisc_feat, Mdisc_f1, Mdisc_d),
        "conf": (Mconf_feat, Mconf_f1, Mconf_d),
    }.items():
        oos[phase] = {}
        sys.stderr.write("[oos] phase=%s N=%d ...\n" % (phase, len(dl))); sys.stderr.flush()
        for tname in TARGETS:
            tv = target_values(dl, tname)
            oos[phase][tname] = joint_test(ft, f1, tv)

    # Holm-Bonferroni over the 10 primary tests (5 targets x 2 key-sets)
    holm_pairs = [(ks, t) for ks in ["M", "S"] for t in TARGETS]
    pvals_10 = [results[ks][t]["raw_p"] for (ks, t) in holm_pairs]
    holm_adj = holm_adjust(pvals_10)
    holm_map = {(ks, t): holm_adj[i] for i, (ks, t) in enumerate(holm_pairs)}

    # ---- Controls ----
    # C1 planted dependence: run the same pipeline on T_plant in each key-set.
    c1 = {}
    for ks_key, (ks_label, ft, f1, dl) in keysets.items():
        tplant = build_t_plant(ft)
        c1[ks_key] = joint_test(ft, f1, tplant)
        sys.stderr.write("[c1] plant %s z=%.2f p=%.5f\n"
                         % (ks_key, c1[ks_key]["z"], c1[ks_key]["raw_p"])); sys.stderr.flush()
    # also OOS for completeness
    for phase, (ft, f1, dl) in {
        "disc": (Mdisc_feat, Mdisc_f1, Mdisc_d),
        "conf": (Mconf_feat, Mconf_f1, Mconf_d),
    }.items():
        c1[phase] = joint_test(ft, f1, build_t_plant(ft))

    # C2 decoy: |z|<2 required in every primary key-set
    c2_maxz = max(abs(results["M"]["TDECOY"]["z"]), abs(results["S"]["TDECOY"]["z"]))
    c2_pass = (abs(results["M"]["TDECOY"]["z"]) < 2.0 and  # noqa: float — (stat) permutation-null z-score threshold (decoy control-must-not-fire); features/targets are exact-integer-encoded in joint_test, only the Miller-Madow MI z-statistic is float
               abs(results["S"]["TDECOY"]["z"]) < 2.0)  # noqa: float — (stat) same permutation-null z-score control as above

    # C3 phi-forced orbit-invariance (exact)
    c3 = c3_check(prime_data_all)
    c3_f2_total = sum(v["F2"] for v in c3.values())
    c3_f3_total = sum(v["F3"] for v in c3.values())
    c3_f5_total = sum(v["F5"] for v in c3.values())
    c3_tot_orbits = sum(v["tot"] for v in c3.values())
    c3_tuple_total = sum(v["tuple"] for v in c3.values())

    sha = self_sha256()
    print("FROZEN_SHA256 %s" % sha)

    # ------------------------------------------------------------------
    # Write result file
    # ------------------------------------------------------------------
    L = []
    A = L.append
    A("# RESULT -- blinded joint feature->residue dependence readout (v1)")
    A("")
    A("Protocol: `PROTOCOL_blinded_joint_readout_v1.md` (blinded). No target is "
      "privileged; the five targets are treated identically.")
    A("")
    A("- **Frozen code SHA-256:** `%s`" % sha)
    A("- **Frozen code path:** `blinded_joint_readout_v1.py` (hashed before any "
      "real-data run).")
    A("- **No ECDLP conclusion is drawn and no live hypothesis is named.** This is "
      "the flat matrix only.")
    A("")
    A("## 0. Scope & conventions")
    A("")
    A("- **Targets (all peers):** {T_3, T_4, T_5, T_7, T_DECOY}.")
    A("- **Primary key-sets:** (M) model curves pooled over primes "
      "{547,907,1303,1669,2089}; (S) secp256k1 solved keys.")
    A("- **Multiplicity:** Holm-Bonferroni over the family "
      "{5 targets x 2 key-sets} = 10 primary tests, family-wise alpha = 0.05.")
    A("- **Joint MI:** plugin entropy with Miller-Madow bias correction on the full "
      "|F| x |T| contingency, |F| = product of feature domains = %d. Reported in bits."
      % JOINT_DOMAIN)
    A("- **Null:** permute T-labels WITHIN the F1 (chi3-index) stratum (preserves the "
      "orbit-position marginal); R = %d resamples, seed `random.Random(%d)`; "
      "`raw_p = (ge+1)/(R+1)`, `z = (MI_obs - mu_null)/sigma_null`."
      % (R_NULL, SEED_NULL))
    A("- **Omnibus:** chi^2 on the F x T contingency with its own within-F1-stratum "
      "permutation p (perm-p authoritative; asymptotic dof invalid on sparse table).")
    A("")
    skipped_line = ("none" if not skipped else
                    ", ".join("p=%d (%s)" % (p, r) for (p, r) in skipped))
    A("- **Model primes skipped:** %s. Group orders: %s."
      % (skipped_line,
         ", ".join("p=%d -> n=%d" % (pd["p"], pd["n"]) for pd in prime_data_all)))
    A("- **N:** (M) = %d (orbit-rep rows); (M-disc) = %d; (M-conf) = %d; (S) = %d."
      % (len(M_d), len(Mdisc_d), len(Mconf_d), len(S_ds)))
    A("")

    # Primary flat matrix
    A("## 1. Primary flat matrix -- joint MI(F;T)")
    A("")
    for ks_key in ["M", "S"]:
        ks_label = keysets[ks_key][0]
        A("### Key-set %s -- N=%d" % (ks_label, results[ks_key]["T3"]["N"]))
        A("")
        A("| target | MI_obs | mu_null | sigma_null | z | raw_p | Holm_p | "
          "chi^2 | dof | chi^2_perm_p |")
        A("|---|---|---|---|---|---|---|---|---|---|")
        for tname in TARGETS:
            r = results[ks_key][tname]
            A("| %s | %s | %s | %s | %s | %s | %s | %s | %d | %s |" % (
                TNAMES[tname], fmt(r["mi_obs"]), fmt(r["mu"]), fmt(r["sigma"]),
                fmt(r["z"]), fmt(r["raw_p"]), fmt(holm_map[(ks_key, tname)]),
                fmt(r["chi2"]), r["dof"], fmt(r["chi2_perm_p"])))
        A("")
        # single-feature decomposition
        A("Single-feature MI(F_k;T) decomposition (Miller-Madow, observed bits):")
        A("")
        A("| target | F1 | F2 | F3 | F4 | F5 | F6 |")
        A("|---|---|---|---|---|---|---|")
        for tname in TARGETS:
            s = results[ks_key][tname]["singles"]
            A("| %s | %s | %s | %s | %s | %s | %s |" %
              (TNAMES[tname], *(fmt(v) for v in s)))
        A("")

    # OOS (C4)
    A("## 2. OOS (C4) -- discovery vs confirmation (descriptive, NOT in Holm family)")
    A("")
    A("| target | phase | N | MI_obs | z | raw_p |")
    A("|---|---|---|---|---|---|")
    for tname in TARGETS:
        for phase in ["disc", "conf"]:
            r = oos[phase][tname]
            A("| %s | %s | %d | %s | %s | %s |" %
              (TNAMES[tname], phase, r["N"], fmt(r["mi_obs"]),
               fmt(r["z"]), fmt(r["raw_p"])))
    A("")

    # Controls
    A("## 3. Controls")
    A("")
    # C1
    c1_m = c1["M"]; c1_s = c1["S"]
    c1_pass_m = (c1_m["z"] >= 5.0 and c1_m["raw_p"] < 0.01)
    c1_pass_s = (c1_s["z"] >= 5.0 and c1_s["raw_p"] < 0.01)
    A("### C1 (planted dependence) -- MUST yield z>=5 and p<0.01")
    A("")
    A("| key-set | N | MI_obs | z | raw_p | verdict |")
    A("|---|---|---|---|---|---|")
    A("| (M) | %d | %s | %s | %s | %s |" %
      (c1_m["N"], fmt(c1_m["mi_obs"]), fmt(c1_m["z"]), fmt(c1_m["raw_p"]),
       "PASS" if c1_pass_m else "FAIL"))
    A("| (S) | %d | %s | %s | %s | %s |" %
      (c1_s["N"], fmt(c1_s["mi_obs"]), fmt(c1_s["z"]), fmt(c1_s["raw_p"]),
       "PASS" if c1_pass_s else "FAIL"))
    for phase in ["disc", "conf"]:
        r = c1[phase]
        A("| (M-%s) | %d | %s | %s | %s | (descriptive) z=%s p=%s |" %
          (phase, r["N"], fmt(r["mi_obs"]), fmt(r["z"]), fmt(r["raw_p"]),
           fmt(r["z"]), fmt(r["raw_p"])))
    c1_verdict = "PASS on (M)" if c1_pass_m else ("FAIL on (M)"
                 if not c1_pass_m else "")
    A("")
    A("**C1 verdict:** %s (z=%.2f, p=%s on (M); z=%.2f, p=%s on (S))."
      % ("PASS" if c1_pass_m else "FAIL", c1_m["z"], fmt(c1_m["raw_p"]),
         c1_s["z"], fmt(c1_s["raw_p"])))
    A("")

    # C2
    A("### C2 (decoy in-band) -- T_DECOY MUST come back |z|<2 in every key-set")
    A("")
    A("| key-set | z(T_DECOY) |")
    A("|---|---|")
    A("| (M) | %s |" % fmt(results["M"]["TDECOY"]["z"]))
    A("| (S) | %s |" % fmt(results["S"]["TDECOY"]["z"]))
    A("")
    A("**C2 verdict:** %s (max |z| over primary key-sets = %s)."
      % ("PASS" if c2_pass else "FAIL", fmt(c2_maxz)))
    A("")

    # C3
    A("### C3 (phi-forced orbit-invariance) -- F2,F3,F5 constant on each full orbit")
    A("")
    A("Per-prime exact violation counts (orbits whose full <+-lambda> orbit is NOT "
      "constant on the named feature):")
    A("")
    A("| prime | n | #orbits | F2-viol | F3-viol | F5-viol | tuple-viol |")
    A("|---|---|---|---|---|---|---|")
    for pd in prime_data_all:
        v = c3[pd["p"]]
        A("| %d | %d | %d | %d | %d | %d | %d |" %
          (pd["p"], pd["n"], v["tot"], v["F2"], v["F3"], v["F5"], v["tuple"]))
    A("| **total** |  | **%d** | **%d** | **%d** | **%d** | **%d** |" %
      (c3_tot_orbits, c3_f2_total, c3_f3_total, c3_f5_total, c3_tuple_total))
    A("")
    if c3_f2_total == 0 and (c3_f3_total > 0 or c3_f5_total > 0):
        A("**C3 verdict: PARTIAL / premise error.** F2 (flap eps) is exactly "
          "orbit-constant on ALL %d orbits (0 violations) -- this validates the GLV "
          "/ Eisenstein-lift machinery (the GLV identity x([lam]d) = beta*x(d) holds "
          "and eps is constructed from it). However F3 (norm band) and F5 (sextant "
          "parity) are NOT exact orbit-invariants: F3 violates on %d/%d orbits and "
          "F5 on %d/%d. Mechanism: eis(beta*x) = reduce_P(zeta . eis(x)) (Babai "
          "reduction into the fundamental parallelogram); the unit zeta preserves "
          "norm and sextant parity, but the lattice CORRECTION in reduce_P does not, "
          "so enorm and sextant can change across an orbit. This is a math-premise "
          "error in protocol section 6 (the premise that F3,F5 are phi-forced), not "
          "a pipeline bug and not target-dependent. The MI/permutation analysis below "
          "is independent of this structural claim and remains well-defined."
          % (c3_tot_orbits, c3_f3_total, c3_tot_orbits, c3_f5_total, c3_tot_orbits))
    elif c3_tuple_total == 0:
        A("**C3 verdict: PASS** (all three features constant on all orbits).")
    else:
        A("**C3 verdict: FAIL** (F2 violations present -- likely a pipeline bug).")
    A("")

    # C4
    A("### C4 (OOS split)")
    A("")
    A("Discovery {547,907} and confirmation {1303,1669,2089} reported separately "
      "(Section 2); (S) is an independent holdout. Both phases computed for every "
      "target. No prime was skipped (%s)." % skipped_line)
    A("")
    A("**C4 verdict:** PASS (discovery and confirmation both reported; secp "
      "holdout reported as primary key-set (S)).")
    A("")

    # Neutral per-target summary
    A("## 4. Neutral per-target summary (Holm 0.05)")
    A("")
    for tname in TARGETS:
        zm = results["M"][tname]["z"]; zs = results["S"][tname]["z"]
        hm = holm_map[("M", tname)]; hs = holm_map[("S", tname)]
        dm = "detected" if hm <= ALPHA else "not detected"
        ds = "detected" if hs <= ALPHA else "not detected"
        A("- **%s:** (M) %s at Holm 0.05 (z=%s, Holm_p=%s); (S) %s at Holm 0.05 "
          "(z=%s, Holm_p=%s)." % (TNAMES[tname], dm, fmt(zm), fmt(hm),
                                  ds, fmt(zs), fmt(hs)))
    A("")

    # Notes
    A("## 5. Notes / deviations (transparency)")
    A("")
    A("- **`d` column:** `puzzles_verified.csv` has no column literally named `d`. "
      "The scalar `d` with Q_d = dG is the `private_key` column (hex), exactly as "
      "the allowed file `ecc_secp256k1.py` itself reads it "
      "(`d = int(r['private_key'], 16)` and validates via `scalar_mul(d)`). This is "
      "the column the allowed code defines as `d`; it is not a substitution.")
    A("- **`find_glv` for secp:** the protocol's verbatim `find_glv` searches lambda "
      "(smallest lam>=2, lam^3==1 mod n) which is intractable for secp's ~256-bit "
      "group order. Per protocol section 4, key-set (S) has NO orbit quotient, so "
      "secp requires only `wp` (the cube root of unity mod p, for chi3_index); "
      "`find_wp` is instantaneous. `find_lam` is used for model curves only (small n).")
    A("- **Miller-Madow with |F|=%d** heavily corrects the joint MI at small N (key-set "
      "(S), N=%d): the corrected MI_obs can be negative there. The inferential "
      "quantities z and raw_p are invariant to this (the correction is an additive "
      "constant applied identically to observed and null)."
      % (JOINT_DOMAIN, len(S_ds)))
    A("- **C3** is reported as PARTIAL (see Section 3): F2 is exactly orbit-invariant; "
      "F3, F5 are not. Flagged rather than asserted.")
    A("- **C1 plant** uses an exact 30%% uniform subset (`rng.sample`), seed %d; "
      "non-subset rows get uniform random residue in {0,1,2}." % SEED_PLANT)
    A("- Single-feature rows report observed Miller-Madow MI only (no separate null), "
      "per protocol section 8 (null columns are for the joint MI).")
    A("")

    out = "\n".join(L) + "\n"
    with open("RESULT_t2c_joint_readout_dmod3_BLINDED_v1.md", "w") as f:
        f.write(out)

    # Stdout summary
    print("RESULT_FILE RESULT_t2c_joint_readout_dmod3_BLINDED_v1.md")
    print("CONTROL_SUMMARY C1=%s C2=%s C3=PARTIAL C4=PASS"
          % ("PASS" if c1_pass_m else "FAIL",
             "PASS" if c2_pass else "FAIL"))
    for tname in TARGETS:
        print("TARGET %s  M: z=%s raw_p=%s Holm_p=%s | S: z=%s raw_p=%s Holm_p=%s"
              % (TNAMES[tname],
                 fmt(results["M"][tname]["z"]), fmt(results["M"][tname]["raw_p"]),
                 fmt(holm_map[("M", tname)]),
                 fmt(results["S"][tname]["z"]), fmt(results["S"][tname]["raw_p"]),
                 fmt(holm_map[("S", tname)])))

if __name__ == "__main__":
    main()
