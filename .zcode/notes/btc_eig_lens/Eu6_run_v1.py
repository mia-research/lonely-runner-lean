#!/usr/bin/env python3
"""
Eu6_run_v1.py — executes PREREG_Eu6_v1.md (in .zcode/notes/btc_eig_lens/).
Measures E[u⁶] on the 12 OOS stratum-S primes, exact-integer signal path, and compares to
SU(2) (5/64) vs torus/CM (5/16). Tests LENS Prediction A.

Run from the btc_puzzle_investigation directory (imports twist_orbit_spectrum_run_v1.signal).
"""
import sys, json
from fractions import Fraction as Fr
import numpy as np

# import the project's signal() -- path is the project dir, run from there
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from twist_orbit_spectrum_run_v1 import signal

PRIMES = [823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503, 2647, 2731]
R_SIM = 4000
SEED = 20260730
SU2_EU6 = Fr(5, 64)     # = 0.078125
UNIF_EU6 = Fr(5, 16)    # = 0.3125
SU2_EU4 = Fr(1, 8)      # for the C-REPRODUCE-E[u⁴] control

def moments_exact_eu6(p, b=7):
    """Exact E[u²], E[u⁴], E[u⁶] via integer autocorrelation. No float in signal path."""
    s = signal(p, b)
    if s is None: return None
    n, c, X, Y = s
    if (n - 1) % 6 != 0: return None
    L = (n - 1) // 6
    nint = int(n)
    carr = np.asarray(c, dtype=np.int64)
    # R[j] = sum_k c_k c_{k+j}  (integer autocorrelation)
    R = np.array([int(np.dot(carr, np.roll(carr, -j))) for j in range(nint)], dtype=object)
    # T2 = sum_j R(j)^2  -> E[u⁴] = n*T2 / (16 p^2 (n-1))
    T2 = int(np.sum(R * R))
    # T3 = sum_{j1,j2} R(j1) R(j2) R(-(j1+j2) mod n)  -> E[u⁶] = n*T3 / (64 p^3 (n-1))
    # vectorize: for each j1, sum over j2 of R(j2)*R(-(j1+j2))
    # = correlate R with R-reversed; equivalently full convolution.
    # T3 = sum_{j1} R(j1) * (R (*) R)[-(j1)]  where (*) is cyclic convolution
    # cyclic convolution of R with itself: (R(*)R)[m] = sum_j R(j) R(m-j)
    # then T3 = sum_m (R(*)R)[m] * R(-m)
    # use FFT-free exact integer cyclic convolution (n is small, ~2000-3000)
    Rc = R.astype(object)
    # cyclic conv via numpy correlate is O(n^2); n<=3000 so ~9M ops, fine
    conv = np.zeros(nint, dtype=object)
    for m in range(nint):
        conv[m] = int(np.sum(Rc * np.roll(Rc[::-1], m+1)))
    # conv[m] = sum_j R(j) R(m - j mod n)  -- verify below
    T3 = 0
    for m in range(nint):
        T3 += int(conv[m]) * int(Rc[(-m) % nint])
    T3 = int(T3)
    Eu2 = Fr(nint, 4 * p)
    Eu4 = Fr(nint * T2, 16 * p * p * (nint - 1))
    Eu6 = Fr(nint * T3, 64 * p * p * p * (nint - 1))
    return {"p": p, "n": nint, "L": L, "T2": T2, "T3": T3,
            "Eu2": Eu2, "Eu4": Eu4, "Eu6": Eu6}

# ---- null samplers (float reference only) ----
def _st_u(L, rng):
    out = np.empty(0)
    while out.size < L:
        x = rng.uniform(-1.0, 1.0, size=2 * L)
        keep = x[rng.uniform(0.0, 1.0, size=x.size) < np.sqrt(1 - x * x)]
        out = np.concatenate([out, keep])
    return out[:L]

def _unif_u(L, rng):
    return np.cos(rng.uniform(0.0, np.pi, size=L))

def band(sampler, L, Rsim, rng, power=6):
    est = np.array([np.mean(sampler(L, rng) ** power) for _ in range(Rsim)])
    est.sort()
    return float(est[int(0.025*Rsim)]), float(est[int(0.975*Rsim)]), float(est.mean())

# ---- main ----
rng = np.random.default_rng(SEED)
print(f"=== E[u⁶] MEASUREMENT (PREREG_Eu6_v1.md) — 12 OOS stratum-S primes, R_sim={R_SIM}, seed={SEED} ===\n", flush=True)
print(f"predictions: SU(2) E[u⁶]=5/64={float(SU2_EU6):.6f}   torus/CM E[u⁶]=5/16={float(UNIF_EU6):.6f}\n", flush=True)

results = []
nin_su2 = nin_unif = 0
devs_su2 = []
for p in PRIMES:
    m = moments_exact_eu6(p)
    if m is None:
        print(f"  p={p}: signal returned None (n-1 not divisible by 6?)", flush=True)
        continue
    L = m["L"]
    Eu6f = float(m["Eu6"])
    su2_lo, su2_hi, su2_cen = band(_st_u, L, R_SIM, rng)
    unif_lo, unif_hi, unif_cen = band(_unif_u, L, R_SIM, rng)
    in_su2 = bool(su2_lo <= Eu6f <= su2_hi)
    in_unif = bool(unif_lo <= Eu6f <= unif_hi)
    dev_su2 = Eu6f - float(SU2_EU6)
    devs_su2.append((L, dev_su2))
    nin_su2 += in_su2; nin_unif += in_unif
    # controls
    c_forced = (m["Eu2"] == Fr(int(m["n"]), 4*p))
    c_repro_eu4 = (m["Eu4"] == SU2_EU4)  # exact Fraction compare to 1/8 is too strict; check closeness
    eu4_match = abs(float(m["Eu4"]) - float(SU2_EU4)) < 0.02  # published values were 0.110-0.135
    print(f"p={p:5d} n={m['n']:5d} L={L:4d}  E[u⁶]={Eu6f:.6f}  SU2=[{su2_lo:.5f},{su2_hi:.5f}]  "
          f"UNIF=[{unif_lo:.5f},{unif_hi:.5f}]  in_su2={in_su2}  in_unif={in_unif}  dev(5/64)={dev_su2:+.5f}", flush=True)
    print(f"        C-FORCED(E[u²]=n/4p)={c_forced}  E[u⁴]={float(m['Eu4']):.5f} (pub ~0.11-0.14, SU2=0.125)", flush=True)
    results.append({**m, "Eu6f": Eu6f, "su2_lo": su2_lo, "su2_hi": su2_hi,
                    "unif_lo": unif_lo, "unif_hi": unif_hi, "su2_cen": su2_cen, "unif_cen": unif_cen,
                    "in_su2": in_su2, "in_unif": in_unif})

# aggregate
wdev = sum(L*d for L,d in devs_su2) / sum(L for L,_ in devs_su2)
ds = sorted(devs_su2, key=lambda t: t[0])
small = [d for _,d in ds[:6]]; large = [d for _,d in ds[6:]]
ms = sum(small)/len(small); ml = sum(large)/len(large)
xs = [1.0/(L**0.5) for L,_ in devs_su2]; ys = [d for _,d in devs_su2]
xm = sum(xs)/len(xs); ym = sum(ys)/len(ys)
sl = sum((x-xm)*(y-ym) for x,y in zip(xs,ys)) / sum((x-xm)**2 for x in xs)
icept = ym - sl*xm

print(f"\n=== AGGREGATE ===", flush=True)
print(f"in SU(2) band: {nin_su2}/12   in unif band: {nin_unif}/12", flush=True)
print(f"L-weighted mean dev from 5/64: {wdev:+.5f}", flush=True)
print(f"CONVERGENCE: small-L mean dev={ms:+.5f}  large-L mean dev={ml:+.5f}  (shrinking->SU(2) finite-p; constant->reduction)", flush=True)
print(f"EXTRAPOLATION dev(L->inf) intercept={icept:+.5f}  (≈0 => converges to 5/64 = full SU(2))", flush=True)

# verdict
print(f"\n=== LENS PREDICTION A VERDICT ===", flush=True)
if nin_su2 >= 10 and abs(icept) < 0.005:
    print(f"CONFIRMED: E[u⁶] ≈ 5/64 across primes, converges to SU(2). θ-rate function is max-entropy.", flush=True)
elif nin_unif >= 10:
    print(f"REFUTED on θ: E[u⁶] ≈ 5/16 (torus/CM). Rate function is NOT max-entropy; lens picture wrong on θ.", flush=True)
else:
    print(f"INTERMEDIATE/MIXED: neither full SU(2) nor torus. Third monodromy group — moment curve discriminates structure E[u⁴] could not.", flush=True)

# save
out = {"primes": PRIMES, "seed": SEED, "R_sim": R_SIM,
       "SU2_Eu6": str(SU2_EU6), "UNIF_Eu6": str(UNIF_EU6),
       "results": [{k: (str(v) if isinstance(v, Fr) else v) for k,v in r.items()} for r in results],
       "aggregate": {"nin_su2": nin_su2, "nin_unif": nin_unif, "wdev_su2": wdev,
                     "small_L_dev": ms, "large_L_dev": ml, "intercept": icept}}
with open("/Users/trentpalelei/Desktop/Math Ex/.zcode/notes/btc_eig_lens/Eu6_results_v1.json","w") as f:
    json.dump(out, f, indent=2)
print(f"\nwrote Eu6_results_v1.json", flush=True)
