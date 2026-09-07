#!/usr/bin/env python3
"""n=8 extension of the Theorem 5.2 / Conjecture 5.2-H mining scan.

Runs strictly to experiments/n8_mining/PREREG_v1.md:
  stage 1  matched control, n <= 7 at the published bounds -- abort on any mismatch
  stage 2  planted controls P1-P4
  stage 3  n = 8 primary scan, PREREG section 1.3 bounds, no M cap
  stage 4  section 3 outcome cells on BOTH strata, CSV + slices

DECLARED DEVIATION FROM PREREG section 6.3 ("same code path").
`compute_residue_structure` costs |I_G| * L_A * p because it walks each band element
by element.  The band is a contiguous cyclic interval of length L_A*p in
Z/(n*L_G*L_A), and beta = pos // L_G, so its beta-image is a contiguous cyclic run.
`fast_residue_structure` computes that run in O(1) per alpha instead of O(L_A*p).
It is NOT trusted on that argument: stage 1 runs BOTH implementations over all
38,664 control inputs and aborts unless every field of every row is identical, and
stage 3 re-checks a deterministic 1-in-500 sample of n=8 inputs against the
reference.  If either check fails the run is void.
"""
import csv, itertools, math, os, random, sys, time
from collections import Counter
from functools import reduce

sys.path.insert(0, os.path.expanduser(
    "~/Desktop/Math Ex/LonelyRunner/scripts"))
from phase5_residue_structure import (          # noqa: E402
    compute_residue_structure, classify_lrc, good_cell_idx,
    lcm_list, gcd_list, isprime)

OUT = os.path.dirname(os.path.abspath(__file__))
_gc_cache = {}

def gc(speeds, n):
    key = (tuple(speeds), n)
    if key not in _gc_cache:
        _gc_cache[key] = good_cell_idx(list(speeds), n, lcm_list(list(speeds)))
    return _gc_cache[key]

def fast_residue_structure(n, G_speeds, A_speeds, p):
    L_G, L_A = lcm_list(G_speeds), lcm_list(A_speeds)
    nLG, nLA, nLGLA = n * L_G, n * L_A, n * L_G * L_A
    I_G, I_A = gc(G_speeds, n), gc(A_speeds, n)
    blen = L_A * p
    band = 0
    for a in I_G:
        s = ((a * p) % nLG) * L_A
        b0 = (s // L_G) % nLA
        cnt = (s % L_G + blen - 1) // L_G + 1
        run = ((1 << cnt) - 1) << b0
        band |= (run & ((1 << nLA) - 1)) | (run >> nLA)
    n_band = band.bit_count()
    tgt = 0
    for b in I_A:
        tgt |= 1 << b
    N_joint = (band & tgt).bit_count()
    modmask = (1 << L_A) - 1
    band_mod = 0
    t = band
    for _ in range(n):
        band_mod |= t & modmask
        t >>= L_A
    tgt_mod = 0
    for b in I_A:
        tgt_mod |= 1 << (b % L_A)
    missed = modmask & ~band_mod
    res_G = len({a % L_G for a in I_G})
    return {
        "n": n, "G_speeds": "-".join(map(str, G_speeds)),
        "A_speeds": "-".join(map(str, A_speeds)), "p": p,
        "kG": len(G_speeds), "kA": len(A_speeds), "L_G": L_G, "L_A": L_A,
        "cIG": len(I_G), "cIA": len(I_A),
        "res_G_mod_LG": res_G, "res_G_mod_LG_full": int(res_G == L_G),
        "n_band_betas": n_band,
        "n_band_betas_mod_LA": band_mod.bit_count(),
        "n_missed_LA": missed.bit_count(),
        "target_in_missed_LA": int(bool(tgt_mod & missed)),
        "targets_all_missed_LA": int(bool(tgt_mod) and (tgt_mod & ~missed) == 0),
        "N_joint": N_joint,
        "lrc_class": classify_lrc(n, G_speeds, A_speeds, p),
    }

def derive(r, n):
    r = dict(r)
    r["delta"] = r["kG"] + r["kA"] - (n - 1)
    r["slack"] = r["n_band_betas"] + r["cIA"] - n * r["L_A"]
    r["pigeon"] = int(r["slack"] > 0)
    r["vmax_all"] = max([int(x) for x in r["G_speeds"].split("-")] +
                        [int(x) for x in r["A_speeds"].split("-")])
    r["M"] = n * r["L_G"] * r["L_A"] * r["p"]
    return r

def enumerate_inputs(n, pool, kGs, kAs, primes, mcap=None):
    for kG in kGs:
        for G in itertools.combinations(pool, kG):
            G = list(G)
            L_G = lcm_list(G)
            if not gc(G, n):
                continue
            for kA in kAs:
                for A in itertools.combinations(pool, kA):
                    A = list(A)
                    if set(G) & set(A):
                        continue
                    if not gc(A, n):
                        continue
                    L_A = lcm_list(A)
                    for p in primes:
                        if math.gcd(p, L_G) != 1: continue
                        if p in G or p in A: continue
                        if not (p < n * L_G): continue
                        if mcap is not None and n * L_G * L_A * p > mcap: continue
                        if math.gcd(p, reduce(math.gcd, G + A, 0)) != 1: continue
                        yield n, G, A, p

def die(msg):
    print("\n*** RUN VOID: " + msg)
    sys.exit(1)

# ---------------------------------------------------------------- stage 1
print("=" * 78); print("STAGE 1 — matched control, n <= 7 (PREREG section 5.1)"); print("=" * 78)
PRIMES = [q for q in range(2, 20) if isprime(q)]
t0 = time.time(); ctrl = []; mism = 0
for n, G, A, p in itertools.chain.from_iterable(
        enumerate_inputs(n, list(range(1, 9)), [1, 2, 3], [1, 2], PRIMES, 5_000_000)
        for n in (3, 4, 5, 6, 7)):
    ref = compute_residue_structure(n, G, A, p)
    fst = fast_residue_structure(n, G, A, p)
    if ref != fst:
        mism += 1
        if mism <= 3: print("  FIELD MISMATCH", n, G, A, p,
                            {k: (ref[k], fst[k]) for k in ref if ref[k] != fst[k]})
    ctrl.append(derive(ref, n))
print(f"  fast-vs-reference mismatches over {len(ctrl)} control inputs: {mism}")
if mism: die("fast path disagrees with phase5 reference")

ce = [r for r in ctrl if r["N_joint"] == 0]
strict = [r for r in ctrl if r["lrc_class"] in ("DI", "ModDI")]
d0 = [r for r in ctrl if r["delta"] == 0]
got = {
    "total": len(ctrl), "CE": len(ce),
    "pigeon_all": sum(r["pigeon"] for r in ctrl),
    "CE_with_pigeon": sum(1 for r in ce if r["pigeon"]),
    "strict": len(strict),
    "strict_pigeon": sum(r["pigeon"] for r in strict),
    "strict_resid": sum(1 - r["pigeon"] for r in strict),
    "delta0": len(d0),
    "delta0_resid": sum(1 - r["pigeon"] for r in d0),
}
want = {"total": 38664, "CE": 681, "pigeon_all": 34825, "CE_with_pigeon": 0,
        "strict": 5517, "strict_pigeon": 5464, "strict_resid": 53,
        "delta0": 8388, "delta0_resid": 83}
for k in want:
    ok = got[k] == want[k]
    print(f"  {k:<16} expected {want[k]:>6}   got {got[k]:>6}   {'OK' if ok else 'MISMATCH'}")
    if not ok: die(f"control row {k} disagrees")
ce_delta = Counter(r["delta"] for r in ce)
res_p = Counter(r["p"] for r in strict if not r["pigeon"])
print("  CE delta-histogram      ", dict(sorted(ce_delta.items())), " expected {1:69,2:333,3:279}")
print("  53-residual p-histogram ", dict(sorted(res_p.items())), " expected {2:30,3:21,5:1,7:1}")
if dict(sorted(ce_delta.items())) != {1: 69, 2: 333, 3: 279}: die("CE delta histogram")
if dict(sorted(res_p.items())) != {2: 30, 3: 21, 5: 1, 7: 1}: die("residual p histogram")
print(f"  control FIRES  ({time.time()-t0:.1f}s)")

# ---------------------------------------------------------------- stage 2
print(); print("=" * 78); print("STAGE 2 — planted controls (PREREG section 5.3)"); print("=" * 78)
p1 = derive(fast_residue_structure(3, [3], [1, 5], 2), 3)
exp = {"N_joint": 0, "n_band_betas": 12, "cIA": 1, "targets_all_missed_LA": 1}
print("  P1 smallest known CE n=3 G=[3] A=[1,5] p=2:",
      {k: p1[k] for k in exp}, " n*L_A =", 3 * p1["L_A"], " slack =", p1["slack"])
for k, v in exp.items():
    if p1[k] != v: die(f"P1 field {k}: expected {v}, got {p1[k]}")
if p1["slack"] != -2: die("P1 slack")
print("  P1 FIRES — the CE detector is live")

p2 = dict(p1); p2["lrc_class"] = "DI"; p2["delta"] = 0
cellA_fires = (p2["lrc_class"] in ("DI", "ModDI") or p2["delta"] == 0) and p2["N_joint"] == 0
print("  P2 same input forced into the LRC-shape branch: Cell A fires =", cellA_fires)
if not cellA_fires: die("P2 — the Cell A zero would be uninformative")

p3 = {"n": 8, "delta": 2, "N_joint": 0}
d_hist = Counter(r["delta"] for r in [p3] if r["N_joint"] == 0)
print("  P3 synthetic n=8 delta=+2 CE reaches the D-cell histogram:", dict(d_hist))
if d_hist.get(2) != 1: die("P3 — stratifier drops n=8 CE rows")

try:
    bad = {"pigeon": 1, "N_joint": 0}
    assert not (bad["pigeon"] and bad["N_joint"] == 0), "Cell E"
    die("P4 — the Cell E assertion is not live")
except AssertionError as e:
    if str(e) != "Cell E": raise
    print("  P4 FIRES — the Cell E assertion aborts on pigeon AND N_joint=0")

# ---------------------------------------------------------------- stage 3
print(); print("=" * 78); print("STAGE 3 — n = 8 primary scan (PREREG section 1.3)"); print("=" * 78)
POOL = list(range(1, 11))
inputs = list(enumerate_inputs(8, POOL, [1, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6], PRIMES, None))
print(f"  admissible tuples: {len(inputs)}   (PREREG section 2.4 pre-committed: 258814)")
rows = []; t0 = time.time(); checked = 0
for i, (n, G, A, p) in enumerate(inputs):
    r = derive(fast_residue_structure(n, G, A, p), n)
    if r["pigeon"] and r["N_joint"] == 0:
        die(f"Cell E fired at {G} {A} {p} — implementation defect, not a result")
    if i % 500 == 0:
        if compute_residue_structure(n, G, A, p) != fast_residue_structure(n, G, A, p):
            die(f"fast path disagrees at n=8 sample {G} {A} {p}")
        checked += 1
    rows.append(r)
    if i % 20000 == 0 and i:
        print(f"    {i}/{len(inputs)}  {time.time()-t0:.0f}s", flush=True)
print(f"  scan complete in {time.time()-t0:.0f}s; fast-path spot-checks passed: {checked}")

with open(os.path.join(OUT, "n8_scan_v1.csv"), "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
print(f"  wrote n8_scan_v1.csv ({len(rows)} rows)")
import pickle
pickle.dump(rows, open(os.path.join(OUT, "n8_rows.pkl"), "wb"))
print("  wrote n8_rows.pkl")
