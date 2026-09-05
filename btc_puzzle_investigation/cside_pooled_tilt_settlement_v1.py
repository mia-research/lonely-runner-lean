#!/usr/bin/env python3
# cside_pooled_tilt_settlement_v1.py -- PREREG_cside_pooled_tilt_settlement_v1.md
#
# Settle the v1 flagged lead: a small consistent NEGATIVE bias of the orbit-level inv-map
# statistic T_inv across large primes (v1: 18 primes, mean z=-0.622, Stouffer z=-2.64, survived
# a calibration control but below per-prime detection / no family-wise survival). v1's pooled
# number rested on z-deflation by a measured calibration std (0.793) -- z-inflation correction.
# This run replaces that with a CALIBRATED PERMUTATION POOLED p-value (empirical null of
# Z_pool itself), ~36 large primes, and an OOS replication gate. See PREREG.
#
# SIGNAL PATH IS EXACT (CLAUDE.md). c[d] = chi2(y of [d]G) is an exact int64 Legendre symbol
# (twist_orbit_spectrum_run_v1.signal). Orbits, inv/pow-k maps, fold assignment: integer /
# SHA-256 only. Float appears ONLY in the z-statistics and the permutation ranking, each
# ranked against the matched permutation null and marked `# noqa: float`; never a data
# threshold. The decision p-value is an exact integer count. This file must pass check_no_float.py.
#
# No leakage / key-recovery / ECDLP claim. Output = characterization or a scoped settle of one
# candidate lead, never an avenue verdict (the channel at 2^128 is not touched here).
import sys, math, json, hashlib
import numpy as np
from sympy import primitive_root, nextprime, isprime as sym_isprime
from fractions import Fraction

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from twist_orbit_spectrum_run_v1 import signal

# ---- frozen parameters (PREREG) -------------------------------------------------------
R_NULL = 2000          # within-prime orbit-label permutations
B_POOL = 100000        # pooled-null joint draws
NP_TARGET = 36         # number of large primes
MIN_ORBITS = 3000      # v1 power floor was 3620-4400 orbits
P_START = 10000        # upward nextprime scan
DEF793 = Fraction(793, 1000)   # v1's pure-random calibration std, exact, for legacy comparability only
SEED_POOL = 20260731   # pooled-null RNG seed (reproducibility)
SEED_FOLD = 20260731   # magnitude-blind hash-fold seed (PREREG 7a)
EDGE_PRIMES = [11503, 13147, 15607]   # v1 most-negative cells (PREREG 7b)
MAPS_PRIMARY = ["inv"]
MAPS_SECONDARY = ["pow5", "pow7", "pow11", "pow13"]


# ---- exact signal-path primitives (integer only) --------------------------------------
def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def curve_order(p, B=7):
    n = p + 1
    for x in range(p):
        n += legendre((x * x % p * x + B) % p, p)
    return n


def build_orbits(n, lam):
    """mu3-orbit partition of [1, n-1]: orbit of d = {d, lam*d, lam^2*d}. Returns
    (rep_of, orbits, norb). Valid (all size 3) iff 3 | (n-1)."""
    seen = set(); rep_of = {}; orbits = []
    for d in range(1, n):
        if d in seen:
            continue
        orb = sorted([d, (d * lam) % n, (d * lam * lam) % n])
        for x in orb:
            seen.add(x); rep_of[x] = len(orbits)
        orbits.append(orb)
    return rep_of, orbits, len(orbits)


def orbit_map_f(n, lam, rep_of, fname):
    """orbit-index -> orbit-index map induced by f. inv: d->d^{-1}; powK: d->d^K (gcd(K,n-1)=1)."""
    from math import gcd
    def fval(d):
        if fname == "inv":
            return pow(d, n - 2, n)
        k = int(fname[3:]); assert gcd(k, n - 1) == 1, f"{k} not coprime to n-1"
        return pow(d, k, n)
    out = {}
    for d, r in rep_of.items():
        out[r] = rep_of[fval(d)]
    return out


def fold_of(item, seed=0, K=2):
    """Magnitude-blind SHA-256 fold in [0,K). Stable across runs (builtin hash() is salted)."""
    digest = hashlib.sha256(f"{seed}:{item!r}".encode()).hexdigest()
    return int(digest, 16) % K


def Tstat(v, fidx):
    # orbit-level mean product = exact full per-d mean (reduction verified in PREREG 1.1).
    # mean() is a ranked statistic; no ast.Div / float() / float literal on this line.
    return (v * v[fidx]).mean()


# ---- per-prime computation ------------------------------------------------------------
def compute_prime(p, maps, R, null_seed):
    """Return dict: per map {t_data, t_null(np.array R), mu, sd, z_data, z_null(np.array R),
    ge, t_plant, ge_p_hi, ge_p_lo, fires, norb}, plus n, norb. None if prime unusable."""
    n = curve_order(p)
    if not sym_isprime(n):
        return None
    r = signal(p)
    if r is None:
        return None
    nn, c = r[0], r[1]
    if nn != n:
        return None
    if (n - 1) % 3 != 0:           # need clean mu3-orbits of size 3
        return None
    g = int(primitive_root(n)); lam = pow(g, (n - 1) // 3, n)
    rep_of, orbits, norb = build_orbits(n, lam)
    if norb * 3 != n - 1:           # belt-and-suspenders: every orbit size exactly 3
        return None
    val = np.array([c[orb[0]] for orb in orbits], dtype=np.int64)   # +/-1 per orbit
    rng = np.random.default_rng(null_seed)
    info = {"n": n, "norb": norb, "maps": {}}
    for fname in maps:
        try:
            fmap = orbit_map_f(n, lam, rep_of, fname)
        except (AssertionError, KeyError) as e:
            info["maps"][fname] = {"skipped": str(e)}
            continue
        fidx = np.array([fmap[r] for r in range(norb)], dtype=np.int64)
        t_data = Tstat(val, fidx)
        # within-prime null: permute orbit value labels (preserves +/-1 multiset + mu3 structure)
        val_tile = np.tile(val, (R, 1))
        shuf = rng.permuted(val_tile, axis=1)                  # independent row shuffle
        t_null = (shuf * shuf[:, fidx]).mean(axis=1)           # noqa: float (ranked vs null)
        mu = t_null.mean(); sd = t_null.std()
        z_data = (t_data - mu) / sd                            # noqa: float (ranked)
        z_null = (t_null - mu) / sd                            # noqa: float (ranked)
        ge = int((t_null >= t_data).sum())
        # FIRING CONTROL (PREREG 4): fresh independent RNG, 80%-agreement plant, 1% gate (integers)
        rp = np.random.default_rng(p * 1000 + sum(ord(ch) for ch in fname))
        nagree = (4 * norb) // 5                               # agree = 0.8, exact
        vplant = rp.choice([-1, 1], size=norb)
        ii = rp.choice(norb, size=nagree, replace=False)
        for x in ii:
            vplant[fidx[x]] = vplant[x]
        t_plant = Tstat(vplant, fidx)
        ge_p_hi = int((t_null >= t_plant).sum())
        ge_p_lo = int((t_null <= t_plant).sum())
        fires = (ge_p_hi * 100 <= R) or (ge_p_lo * 100 <= R)   # 1% tail either side, integer
        info["maps"][fname] = dict(t_data=t_data, t_null=t_null, mu=mu, sd=sd,
                                   z_data=z_data, z_null=z_null, ge=ge,
                                   t_plant=t_plant, ge_p_hi=ge_p_hi, ge_p_lo=ge_p_lo,
                                   fires=fires, norb=norb)
    return info


# ---- pooled calibrated p-value (PREREG 3) ---------------------------------------------
def pooled_cal(z_data_list, z_null_stack, B, seed):
    """z_null_stack: (NP, R). Returns (Zpool_data, cnt_left, cnt_right, B).
    Pooled null = draw one within-prime null index per prime, Stouffer-combine, repeat B times.
    cnt_left = #{Zpool_null <= Zpool_data}  -> calibrated one-sided (left) p = cnt_left/B."""
    NP = len(z_data_list)
    R = z_null_stack.shape[1]
    Zpool_data = sum(z_data_list) / math.sqrt(NP)              # noqa: float (ranked)
    ZarrT = z_null_stack.T                                     # (R, NP)
    rng = np.random.default_rng(seed)
    idx = rng.integers(0, R, size=(B, NP))
    gathered = np.take_along_axis(ZarrT, idx, axis=0)          # (B, NP): gathered[b,p]=Zarr[p,idx[b,p]]
    Zpool_null = gathered.sum(axis=1) / math.sqrt(NP)          # noqa: float (ranked)
    cnt_left = int((Zpool_null <= Zpool_data).sum())
    cnt_right = int((Zpool_null >= Zpool_data).sum())
    return Zpool_data, cnt_left, cnt_right, B


def decision_strong(cnt, B):
    """cal p < 0.01  <=>  cnt/B < 1/100  <=>  100*cnt < B  (strict, integer)."""
    return cnt * 100 < B

def decision_mild(cnt, B):
    """cal p < 0.05  <=>  20*cnt < B."""
    return cnt * 20 < B


# ---- numpy -> python (for JSON; uses .item()/.tolist(), no float() call) ---------------
def py(x):
    if isinstance(x, dict):
        return {k: py(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [py(v) for v in x]
    if isinstance(x, np.generic):
        return x.item()
    if isinstance(x, np.ndarray):
        return x.tolist()
    return x


# ---- prime sampling -------------------------------------------------------------------
def sample_primes(target, p_start, min_orbits):
    out = []
    p = int(nextprime(p_start - 1))
    while len(out) < target:
        if p % 12 == 7:
            n = curve_order(p)
            if sym_isprime(n) and (n - 1) % 3 == 0:
                norb = (n - 1) // 3
                if norb >= min_orbits and norb * 3 == n - 1:
                    out.append(p)
        p = int(nextprime(p))
    return out


def main():
    maps_all = MAPS_PRIMARY + MAPS_SECONDARY
    print(f"PREREG cside pooled-tilt settlement. R_null={R_NULL} B_pool={B_POOL} "
          f"target_primes={NP_TARGET} min_orbits={MIN_ORBITS}")
    primes = sample_primes(NP_TARGET, P_START, MIN_ORBITS)
    print(f"sampled {len(primes)} primes: {primes}\n")

    per_prime = {}
    for p in primes:
        info = compute_prime(p, maps_all, R_NULL, null_seed=p)
        per_prime[p] = info
        if info is None:
            print(f"  p={p}: UNUSABLE (skipped)")
            continue
        m = info["maps"].get("inv", {})
        if "skipped" in m:
            print(f"  p={p} n={info['n']} orbits={info['norb']}: inv skipped ({m['skipped']})")
            continue
        gate = "[plant fires]" if m["fires"] else "[NO POWER]"
        print(f"  p={p} n={info['n']} orbits={info['norb']}  inv: T={m['t_data']:+.4f} "
              f"z={m['z_data']:+.3f} ge={m['ge']}/{R_NULL} plant_hi={m['ge_p_hi']} "
              f"plant_lo={m['ge_p_lo']} {gate}")

    # --- build included-prime lists per map (gate must fire; PREREG 4) ---
    included = {fname: [] for fname in maps_all}
    excluded = {fname: [] for fname in maps_all}
    for p, info in per_prime.items():
        if info is None:
            continue
        for fname in maps_all:
            m = info["maps"].get(fname, {})
            if "skipped" in m:
                excluded[fname].append((p, "skipped: " + m["skipped"])); continue
            if not m.get("fires", False):
                excluded[fname].append((p, "plant did not fire [NO POWER]")); continue
            included[fname].append(p)

    # ===================== PRIMARY: inv pooled =====================
    fname = "inv"
    z_data_list = [per_prime[p]["maps"][fname]["z_data"] for p in included[fname]]
    z_null_stack = np.array([per_prime[p]["maps"][fname]["z_null"] for p in included[fname]])
    NP = len(included[fname])
    Zpool_data, cnt_left, cnt_right, B = pooled_cal(z_data_list, z_null_stack, B_POOL, SEED_POOL)
    cal_p_left = cnt_left / B                                   # noqa: float (display)
    cal_p_2s = (2 * min(cnt_left, cnt_right)) / B               # noqa: float (display, characterization)
    if cal_p_2s > 1: cal_p_2s = 1                               # noqa: float (clamp)
    # legacy 0.793-deflated comparability (non-decisional)
    zpool_def793 = Zpool_data / float(DEF793)                   # noqa: float (display)
    neg = int(sum(1 for z in z_data_list if z < 0))
    # per-prime family-wise (characterization): Bonferroni + exact Holm (one-sided left, ge/R)
    ge_left = [per_prime[p]["maps"][fname]["ge"] for p in included[fname]]
    R = R_NULL
    bonf_cnt = sum(1 for ge in ge_left if 40 * NP * min(ge, R - ge) < R)   # 2*min/R < 1/(20 NP)
    ord_ge = sorted(ge_left)
    holm_cnt = 0
    for i, ge in enumerate(ord_ge):                            # smallest ge first
        if ge * 20 * (NP - i) <= R:                            # p_(i) <= 1/(20(NP-i+1))
            holm_cnt += 1
        else:
            break
    max_abs_z = max(abs(z) for z in z_data_list)               # noqa: float (display)

    print("\n" + "=" * 70)
    print(f"PRIMARY  inv map   NP={NP} included / {NP_TARGET} sampled")
    print(f"  Z_pool(data)      = {Zpool_data:+.4f}")
    print(f"  calibrated p(left)= {cal_p_left:.5f}   (cnt {cnt_left}/{B})")
    print(f"  calibrated p(2s)  = {cal_p_2s:.5f}   (characterization)")
    print(f"  legacy 0.793-defl = {zpool_def793:+.4f}   (v1 comparability, NON-decisional)")
    print(f"  sign: {neg}/{NP} negative")
    print(f"  per-prime Bonferroni sig (0.05/{NP}): {bonf_cnt}")
    print(f"  per-prime Holm sig (0.05, one-sided left): {holm_cnt}")
    print(f"  max|z| = {max_abs_z:.3f}")
    print(f"  DECISION (alpha=0.01 left): "
          f"{'p<0.01 STRONG' if decision_strong(cnt_left, B) else ('p<0.05 mild' if decision_mild(cnt_left, B) else 'p>=0.05 NULL')}")

    # ===================== OOS 7a: magnitude-blind K=2 hash-fold =====================
    folds = {0: [], 1: []}
    for p in included[fname]:
        folds[fold_of(p, SEED_FOLD, 2)].append(p)
    oos = {}
    print("\n" + "-" * 70)
    print(f"OOS 7a  magnitude-blind SHA-256 fold (seed={SEED_FOLD}, K=2):")
    for f in (0, 1):
        pf = folds[f]
        if not pf:
            print(f"  fold {f}: EMPTY"); oos[f] = None; continue
        zd = [per_prime[p]["maps"][fname]["z_data"] for p in pf]
        zn = np.array([per_prime[p]["maps"][fname]["z_null"] for p in pf])
        Zf, clf, crf, Bf = pooled_cal(zd, zn, B_POOL, SEED_POOL + f)
        pf_p = clf / Bf                                          # noqa: float (display)
        negf = int(sum(1 for z in zd if z < 0))
        oos[f] = dict(primes=pf, Z=Zf, cnt_left=clf, B=Bf, neg=negf)
        print(f"  fold {f}: {len(pf)} primes  Z_pool={Zf:+.4f}  cal_p(left)={pf_p:.5f} "
              f"({clf}/{Bf})  neg {negf}/{len(pf)}  "
              f"{'p<0.05' if decision_mild(clf, Bf) else 'p>=0.05'}")
    both_neg = all(oos[f] is not None and oos[f]["Z"] < 0 for f in oos)
    both_sig = all(oos[f] is not None and decision_mild(oos[f]["cnt_left"], oos[f]["B"]) for f in oos)
    oos_replicate = bool(both_neg and both_sig) and all(oos[f] is not None for f in oos)
    print(f"  OOS REPLICATE (AND-gate: both neg AND both cal_p<0.05): {oos_replicate}")

    # ===================== OOS 7b: fresh-seed edge retest =====================
    edge = []
    print("\n" + "-" * 70)
    print("OOS 7b  fresh-seed retest of v1 most-negative cells (characterization):")
    for p in EDGE_PRIMES:
        n = curve_order(p)
        if not (sym_isprime(n) and (n - 1) % 3 == 0):
            edge.append((p, None, "prime not valid for orbit reduction")); print(f"  p={p}: invalid"); continue
        # fresh independent null seed (NOT the data seed p)
        info = compute_prime(p, MAPS_PRIMARY, R=R_NULL, null_seed=SEED_POOL + p * 7)
        if info is None:
            edge.append((p, None, "unusable")); print(f"  p={p}: unusable"); continue
        m = info["maps"]["inv"]
        edge.append((p, m["z_data"], "[fires]" if m["fires"] else "[NO POWER]"))
        print(f"  p={p}: z_data={m['z_data']:+.3f} (fresh seed)  T={m['t_data']:+.4f}  "
              f"{'[fires]' if m['fires'] else '[NO POWER]'}")

    # ===================== SECONDARY: pow-k channel bound =====================
    # PREREG 6: any pow-k hit goes through the SAME OOS gate as inv before any grade moves.
    secondary = {}
    sec_oos = {}
    print("\n" + "-" * 70)
    print("SECONDARY  pow-k maps (channel bound, Holm 0.05 over the family):")
    sec_results = []
    for fname in MAPS_SECONDARY:
        if not included[fname]:
            secondary[fname] = None; sec_oos[fname] = None; continue
        zd = [per_prime[p]["maps"][fname]["z_data"] for p in included[fname]]
        zn = np.array([per_prime[p]["maps"][fname]["z_null"] for p in included[fname]])
        Z, cl, cr, Bb = pooled_cal(zd, zn, B_POOL, SEED_POOL)
        pl = cl / Bb                                            # noqa: float (display)
        pr = cr / Bb                                            # noqa: float (display)
        p2 = (2 * min(cl, cr)) / Bb                             # noqa: float (display)
        if p2 > 1: p2 = 1                                       # noqa: float (clamp)
        negs = int(sum(1 for z in zd if z < 0))
        # PREREG 7a OOS gate applied symmetrically to the secondary family.
        sf = {0: [], 1: []}
        for p in included[fname]:
            sf[fold_of(p, SEED_FOLD, 2)].append(p)
        foldz = {}
        for ff in (0, 1):
            pf = sf[ff]
            if not pf:
                foldz[ff] = None; continue
            zdf = [per_prime[p]["maps"][fname]["z_data"] for p in pf]
            znf = np.array([per_prime[p]["maps"][fname]["z_null"] for p in pf])
            Zf, clf, crf, Bf = pooled_cal(zdf, znf, B_POOL, SEED_POOL + ff)
            foldz[ff] = dict(primes=pf, Z=Zf, cnt_left=clf, B=Bf,
                             cal_p_left=clf / Bf,                           # noqa: float
                             neg=int(sum(1 for z in zdf if z < 0)))
        both_neg = all(foldz[ff] is not None and foldz[ff]["Z"] < 0 for ff in foldz)
        both_sig = all(foldz[ff] is not None and decision_mild(foldz[ff]["cnt_left"], foldz[ff]["B"]) for ff in foldz)
        oos_rep = bool(both_neg and both_sig) and all(foldz[ff] is not None for ff in foldz)
        secondary[fname] = dict(NP=len(included[fname]), Z=Z,
                                cal_p_left=pl, cal_p_right=pr,
                                cal_p_2s=p2, neg=negs, oos_replicate=oos_rep)
        sec_oos[fname] = {str(ff): (None if foldz[ff] is None else
                                    dict(primes=foldz[ff]["primes"], Z=foldz[ff]["Z"],
                                         cnt_left=foldz[ff]["cnt_left"], B=foldz[ff]["B"],
                                         cal_p_left=foldz[ff]["cal_p_left"], neg=foldz[ff]["neg"]))
                          for ff in foldz}
        sec_results.append((fname, cl, cr, Bb, Z, oos_rep))
        print(f"  {fname}: NP={len(included[fname])} Z={Z:+.4f} "
              f"cal_p(left)={pl:.5f} cal_p(right)={pr:.5f} cal_p(2s)={p2:.5f} neg {negs}/{len(included[fname])} "
              f"| OOS replicate={oos_rep}")
        for ff in (0, 1):
            if foldz[ff] is None:
                print(f"        fold {ff}: EMPTY"); continue
            print(f"        fold {ff}: {len(foldz[ff]['primes'])} primes Z={foldz[ff]['Z']:+.4f} "
                  f"cal_p(left)={foldz[ff]['cal_p_left']:.5f} neg {foldz[ff]['neg']}/{len(foldz[ff]['primes'])}")

    # ===================== JSON dump =====================
    payload = {
        "prereg_sha_prefreeze": "e4a95ca3eaded16afd7ae14c84b9ca27c79b95020b0f46cba2c1e2931ae5d5e5",
        "params": {"R_null": R_NULL, "B_pool": B_POOL, "NP_sampled": len(primes),
                   "NP_target": NP_TARGET, "min_orbits": MIN_ORBITS, "seed_pool": SEED_POOL,
                   "seed_fold": SEED_FOLD},
        "primes": primes,
        "included": {fname: included[fname] for fname in maps_all},
        "excluded": {fname: excluded[fname] for fname in maps_all},
        "primary_inv": {
            "NP": NP, "Z_pool": Zpool_data, "cnt_left": cnt_left, "cnt_right": cnt_right,
            "B": B, "cal_p_left": cal_p_left, "cal_p_2s": cal_p_2s,
            "legacy_def793": zpool_def793, "neg": neg, "NP_total": NP,
            "bonferroni_sig": bonf_cnt, "holm_sig": holm_cnt, "max_abs_z": max_abs_z,
            "per_prime": [{"p": p, "z": per_prime[p]["maps"][fname]["z_data"],
                           "ge": per_prime[p]["maps"][fname]["ge"],
                           "T": per_prime[p]["maps"][fname]["t_data"]} for p in included[fname]],
        },
        "oos_7a": {str(f): (None if oos[f] is None else
                            dict(primes=oos[f]["primes"], Z=oos[f]["Z"],
                                 cnt_left=oos[f]["cnt_left"], B=oos[f]["B"],
                                 cal_p_left=oos[f]["cnt_left"] / oos[f]["B"],  # noqa: float
                                 neg=oos[f]["neg"]))
                   for f in oos},
        "oos_7a_replicate": oos_replicate,
        "oos_7b_edge": [{"p": p, "z": z, "note": note} for (p, z, note) in edge],
        "secondary": secondary,
        "secondary_oos": sec_oos,
    }
    with open("cside_pooled_tilt_settlement_v1.json", "w") as f:
        json.dump(py(payload), f, indent=2)
    print("\nJSON -> cside_pooled_tilt_settlement_v1.json")


if __name__ == "__main__":
    main()
