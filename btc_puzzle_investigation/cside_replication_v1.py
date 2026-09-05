#!/usr/bin/env python3
"""S5 re-test — pow7 population replication (fresh disjoint primes, pooled OOS).
Executes PREREG_cside_replication_v1.md (frozen SHA c53dced7...).
Instrument imported byte-identical from cside_pooled_tilt_settlement_v1.
DEVIATION: R=2000 (settlement's value, byte-identical + memory-safe) not the prereg's R=20000;
R sets only per-prime null resolution, not the statistic or the pooled decision thresholds.
Signal path exact (int/SHA-256); float only in ranked z / pooled-p vs the permutation null.
"""
import sys, json, math, hashlib
import numpy as np
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from cside_pooled_tilt_settlement_v1 import (curve_order, build_orbits, orbit_map_f,
    Tstat, compute_prime, pooled_cal, sample_primes)
from sympy import nextprime, isprime as sym_isprime
from twist_orbit_spectrum_run_v1 import signal

R = 2000            # per-prime null perms (deviation: settlement value, not prereg 20000)
B = 20000           # pooled-null draws (prereg)
M = 30              # fresh primes (prereg)
MIN_ORBITS = 3000
MAPS = ["pow7", "pow5", "pow11", "pow13"]   # pow7 primary; rest negative controls
J = json.load(open("cside_pooled_tilt_settlement_v1.json"))
ORIG28 = J["included"]["pow7"]              # frozen original pow7 primes

def cal_p_left(zlist, zstack):
    Z, cl, cr, b = pooled_cal(zlist, zstack, B, seed=20260804)
    return Z, cl / b, cr / b

# ---- Gate 0a: instrument-identity (sampling predicate matches settlement) ----
sampled36 = sample_primes(36, 10000, MIN_ORBITS)
id_ok = (sampled36 == J["primes"])
# pow7-28 must be exactly {36 : gcd(7,n-1)=1 and gate fires}; verify gcd on the 28
from math import gcd
gcd_ok = all(gcd(7, curve_order(p) - 1) == 1 for p in ORIG28)
print(f"[Gate0a] sample_primes==json primes: {id_ok} ; gcd(7,n-1)=1 on all 28: {gcd_ok}", flush=True)

# ---- fresh F30: first 30 pow7-usable primes p >= 22004, disjoint from ORIG28 ----
P_start = max(20000, 1 + max(ORIG28))
print(f"[F30] scanning from P_start={P_start}", flush=True)
fresh = {m: [] for m in MAPS}
fresh_z = {m: [] for m in MAPS}
fresh_znull = {m: [] for m in MAPS}
p = int(nextprime(P_start - 1)); scanned = 0
while len(fresh["pow7"]) < M:
    scanned += 1
    if p % 12 == 7:
        info = compute_prime(p, MAPS, R, null_seed=p)
        if info is not None:
            m7 = info["maps"].get("pow7", {})
            if "skipped" not in m7 and m7.get("fires") and p not in ORIG28:
                for mp in MAPS:
                    mm = info["maps"].get(mp, {})
                    if "skipped" not in mm and mm.get("fires"):
                        fresh[mp].append(p)
                        fresh_z[mp].append(mm["z_data"])
                        fresh_znull[mp].append(mm["z_null"])
                if len(fresh["pow7"]) % 5 == 0:
                    print(f"  pow7 usable: {len(fresh['pow7'])}/{M} (p={p})", flush=True)
    p = int(nextprime(p))
print(f"[F30] frozen fresh pow7 primes ({len(fresh['pow7'])}): {fresh['pow7']}", flush=True)

# ---- primary: pooled cal-p for pow7 on F30 ----
out = {"R": R, "B": B, "P_start": P_start, "scanned": scanned,
       "gate0a_sample_id": id_ok, "gate0a_gcd": gcd_ok, "fresh": fresh}
for mp in MAPS:
    zs = fresh_z[mp]; zn = np.array(fresh_znull[mp])
    Z, pl, pr = cal_p_left(zs, zn)
    nneg = int(sum(1 for z in zs if z < 0))
    out[mp] = dict(NP=len(zs), Zpool=Z, cal_p_left=pl, cal_p_right=pr,
                   cal_p_2s=2 * min(pl, pr), nneg=nneg)
    print(f"[{mp}] NP={len(zs)} Zpool={Z:+.3f} cal_p_left={pl:.4f} cal_p_2s={2*min(pl,pr):.4f} "
          f"nneg={nneg}/{len(zs)}", flush=True)

# ---- Gate 0b: firing control (g=1.5 planted anti-corr, pooled) ----
def planted_z(p, g, seed):
    n = curve_order(p); r = signal(p); c = r[1]
    lam = None
    from sympy import primitive_root
    gg = int(primitive_root(n)); lam = pow(gg, (n - 1) // 3, n)
    rep_of, orbits, norb = build_orbits(n, lam)
    fmap = orbit_map_f(n, lam, rep_of, "pow7")
    fidx = np.array([fmap[i] for i in range(norb)], dtype=np.int64)
    rng = np.random.default_rng(int(hashlib.sha256(f"{seed}|p={p}".encode()).hexdigest(), 16) % (2**32))
    v = rng.choice([-1, 1], size=norb)
    val = np.array([c[orb[0]] for orb in orbits], dtype=np.int64)
    sd = None
    # null sd from R perms (reuse settlement style)
    vt = np.tile(val, (R, 1)); shuf = rng.permuted(vt, axis=1)
    tn = (shuf * shuf[:, fidx]).mean(axis=1); mu = tn.mean(); sd = tn.std()
    nplant = round(g * sd * norb)          # |P| ~ g*sd in T-units -> scale to orbit count
    nplant = min(max(nplant, 1), norb // 2)
    ii = rng.choice(norb, size=nplant, replace=False)
    for x in ii: v[fmap[x]] = -v[x]
    tp = Tstat(v, fidx)
    return (tp - mu) / sd
firing_zs = [planted_z(p, 1.5, "fire") for p in fresh["pow7"]]
Zfire = sum(firing_zs) / math.sqrt(len(firing_zs))
out["firing"] = dict(Zpool=Zfire, fires=bool(Zfire < -5.0))
print(f"[Gate0b firing] g=1.5 Zpool={Zfire:+.2f}  fires(<-5)={Zfire < -5.0}", flush=True)

# ---- Gate 0c: negative control (random labels -> null centered) ----
neg_Z = []
for rep in range(50):
    zs = []
    for i, p in enumerate(fresh["pow7"]):
        zn = fresh_znull["pow7"][i]
        rng = np.random.default_rng(int(hashlib.sha256(f"neg|{rep}|{p}".encode()).hexdigest(), 16) % (2**32))
        zs.append(float(zn[rng.integers(0, len(zn))]))   # a random-label draw = a null draw
    neg_Z.append(sum(zs) / math.sqrt(len(zs)))
out["negctrl"] = dict(meanZ=float(np.mean(neg_Z)), ok=bool(abs(np.mean(neg_Z)) < 0.25))
print(f"[Gate0c neg] meanZpool over 50={np.mean(neg_Z):+.3f}  ok(|.|<0.25)={abs(np.mean(neg_Z))<0.25}", flush=True)

# ---- combined (decision-inert) ----
orig_z_note = "original per-prime z not stored in json; combined effect-size not reconstructed here"
out["combined_note"] = orig_z_note

# ---- decision (Sec.9) ----
pf = out["pow7"]["cal_p_left"]
gate0 = (id_ok and gcd_ok and out["firing"]["fires"] and out["negctrl"]["ok"]
         and all(out[m]["cal_p_2s"] > 0.05 for m in ["pow5", "pow11", "pow13"]))
if not gate0:
    verdict = "INVALID RUN (Gate 0 failed)"
elif out["pow7"]["Zpool"] > 1.96:
    verdict = "SIGN-REVERSAL ANOMALY"
elif pf < 0.025:
    verdict = "REPLICATE"
elif out["pow7"]["Zpool"] > -1.0:
    verdict = "WASH (not reproduced)"
else:
    verdict = "ABSTAIN (real-but-thinner or noise)"
out["verdict"] = verdict
out["gate0_pass"] = gate0
print(f"\n=== VERDICT: {verdict} ===  (Gate0={gate0}, pow7 Zpool={out['pow7']['Zpool']:+.3f}, p_fresh={pf:.4f})")
json.dump(out, open("cside_replication_v1_results.json", "w"), indent=1, default=float)
print("saved cside_replication_v1_results.json")
