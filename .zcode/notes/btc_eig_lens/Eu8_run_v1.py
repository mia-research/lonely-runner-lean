#!/usr/bin/env python3
"""
Eu8_run_v1.py — executes PREREG_Eu8_v1.md (.zcode/notes/btc_eig_lens/).
Measures E[u⁸] on the 12 OOS stratum-S primes, exact-integer signal path, compares to
SU(2) (7/128) vs torus/CM (35/256). Locks the moment curve at order 8.

T_4 = sum_m (R*R*R)[m] * R(-m), where (R*R*R) is the 3-fold cyclic convolution already
computed for T_3. E[u⁸] = n*T4 / (256 p^4 (n-1)).
"""
import sys, json
from fractions import Fraction as Fr
import numpy as np

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from twist_orbit_spectrum_run_v1 import signal

PRIMES = [823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503, 2647, 2731]
R_SIM = 4000
SEED = 20260730
SU2_EU8  = Fr(7, 128)    # = 0.054688
UNIF_EU8 = Fr(35, 256)   # = 0.136719

def moments_all(p, b=7):
    """Exact E[u²], E[u⁴], E[u⁶], E[u⁸] via integer autocorrelation. No float in signal path."""
    s = signal(p, b)
    if s is None: return None
    n, c, X, Y = s
    if (n - 1) % 6 != 0: return None
    L = (n - 1) // 6
    nint = int(n)
    carr = np.asarray(c, dtype=np.int64)
    R = np.array([int(np.dot(carr, np.roll(carr, -j))) for j in range(nint)], dtype=object)
    Rc = R.astype(object)
    T2 = int(np.sum(R * R))
    # cyclic convolution R*R  (size n)
    conv2 = np.zeros(nint, dtype=object)
    for m in range(nint):
        conv2[m] = int(np.sum(Rc * np.roll(Rc[::-1], m + 1)))
    # T3 = sum_m conv2[m] * R(-m)   [conv2[m] = (R*R)[m] = sum_j R(j)R(m-j)]
    T3 = int(sum(int(conv2[m]) * int(Rc[(-m) % nint]) for m in range(nint)))
    # cyclic convolution R*R*R : conv3[m] = sum_j conv2[j] * R(m-j)
    conv3 = np.zeros(nint, dtype=object)
    for m in range(nint):
        conv3[m] = int(np.sum(conv2 * np.roll(Rc[::-1], m + 1)))
    # T4 = sum_m conv3[m] * R(-m)
    T4 = int(sum(int(conv3[m]) * int(Rc[(-m) % nint]) for m in range(nint)))
    Eu2 = Fr(nint, 4 * p)
    Eu4 = Fr(nint * T2, 16 * p * p * (nint - 1))
    Eu6 = Fr(nint * T3, 64 * p * p * p * (nint - 1))
    Eu8 = Fr(nint * T4, 256 * p ** 4 * (nint - 1))
    return {"p": p, "n": nint, "L": L, "T2": T2, "T3": T3, "T4": T4,
            "Eu2": Eu2, "Eu4": Eu4, "Eu6": Eu6, "Eu8": Eu8}

def _st_u(L, rng):
    out = np.empty(0)
    while out.size < L:
        x = rng.uniform(-1.0, 1.0, size=2 * L)
        keep = x[rng.uniform(0.0, 1.0, size=x.size) < np.sqrt(1 - x * x)]
        out = np.concatenate([out, keep])
    return out[:L]

def _unif_u(L, rng):
    return np.cos(rng.uniform(0.0, np.pi, size=L))

def band(sampler, L, Rsim, rng, power=8):
    est = np.array([np.mean(sampler(L, rng) ** power) for _ in range(Rsim)])
    est.sort()
    return float(est[int(0.025 * Rsim)]), float(est[int(0.975 * Rsim)]), float(est.mean())

# ---- sanity check T4 vs float FFT on p=127 BEFORE the 12-prime run ----
print("=== C-CROSS sanity (p=127): integer T4 vs float FFT sum|V|^8/n ===", flush=True)
sm = moments_all(127)
V = np.fft.fft(np.asarray(signal(127, 7)[1], dtype=np.complex128))
T4_float = float(((V.real**2 + V.imag**2)**4).sum()) / 127
print(f"  T4 (integer)={sm['T4']}   T4 (float FFT/n)={T4_float:.1f}   match={abs(sm['T4']-T4_float)<0.5}", flush=True)
# also re-verify T2,T3
print(f"  T2 (integer)={sm['T2']}   T3 (integer)={sm['T3']}  (T3 float FFT/n = {float(((V.real**2+V.imag**2)**3).sum())/127:.1f})", flush=True)
assert abs(sm['T4'] - T4_float) < 0.5, "T4 derivation mismatch -- abort"

rng = np.random.default_rng(SEED)
print(f"\n=== E[u⁸] MEASUREMENT (PREREG_Eu8_v1.md) — 12 OOS stratum-S primes, R_sim={R_SIM}, seed={SEED} ===\n", flush=True)
print(f"predictions: SU(2) E[u⁸]=7/128={float(SU2_EU8):.6f}   torus/CM E[u⁸]=35/256={float(UNIF_EU8):.6f}\n", flush=True)

results = []
nin_su2 = nin_unif = 0
devs = []
# load Eu6 results for the C-REPRODUCE-E[u⁶] cross-run repro check
eu6 = json.load(open("/Users/trentpalelei/Desktop/Math Ex/.zcode/notes/btc_eig_lens/Eu6_results_v1.json"))
eu6_by_p = {int(r["p"]): r for r in eu6["results"]}

for p in PRIMES:
    m = moments_all(p)
    if m is None: continue
    L = m["L"]
    Eu8f = float(m["Eu8"])
    su2_lo, su2_hi, su2_cen = band(_st_u, L, R_SIM, rng)
    unif_lo, unif_hi, unif_cen = band(_unif_u, L, R_SIM, rng)
    in_su2 = bool(su2_lo <= Eu8f <= su2_hi)
    in_unif = bool(unif_lo <= Eu8f <= unif_hi)
    dev = Eu8f - float(SU2_EU8)
    devs.append((L, dev))
    nin_su2 += in_su2; nin_unif += in_unif
    c_forced = (m["Eu2"] == Fr(int(m["n"]), 4 * p))
    # cross-run repro: E[u⁶] should match Eu6_results_v1.json exactly (same R)
    eu6_prev = eu6_by_p[p]["Eu6"]
    eu6_match = (str(m["Eu6"]) == eu6_prev)
    print(f"p={p:5d} n={m['n']:5d} L={L:4d}  E[u⁸]={Eu8f:.6f}  SU2=[{su2_lo:.5f},{su2_hi:.5f}]  "
          f"UNIF=[{unif_lo:.5f},{unif_hi:.5f}]  in_su2={in_su2}  in_unif={in_unif}  dev(7/128)={dev:+.5f}", flush=True)
    print(f"        C-FORCED={c_forced}  E[u⁴]={float(m['Eu4']):.5f}  E[u⁶]={float(m['Eu6']):.5f}  C-REPRO-E[u⁶]={eu6_match}", flush=True)
    results.append({**m, "Eu8f": Eu8f, "su2_lo": su2_lo, "su2_hi": su2_hi,
                    "unif_lo": unif_lo, "unif_hi": unif_hi, "in_su2": in_su2, "in_unif": in_unif})

wdev = sum(L * d for L, d in devs) / sum(L for L, _ in devs)
ds = sorted(devs, key=lambda t: t[0])
small = [d for _, d in ds[:6]]; large = [d for _, d in ds[6:]]
ms = sum(small) / len(small); ml = sum(large) / len(large)
xs = [1.0 / (L ** 0.5) for L, _ in devs]; ys = [d for _, d in devs]
xm = sum(xs) / len(xs); ym = sum(ys) / len(ys)
sl = sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / sum((x - xm) ** 2 for x in xs)
icept = ym - sl * xm

print(f"\n=== AGGREGATE ===", flush=True)
print(f"in SU(2) band: {nin_su2}/12   in unif band: {nin_unif}/12", flush=True)
print(f"L-weighted mean dev from 7/128: {wdev:+.5f}", flush=True)
print(f"CONVERGENCE: small-L mean dev={ms:+.5f}  large-L mean dev={ml:+.5f}", flush=True)
print(f"EXTRAPOLATION dev(L->inf) intercept={icept:+.5f}", flush=True)
print(f"\n=== LENS PREDICTION (order-8 extension) VERDICT ===", flush=True)
if nin_su2 >= 10 and abs(icept) < 0.005:
    print(f"CONFIRMED: E[u⁸] ≈ 7/128. Moment curve locked at orders 2,4,6,8 = full SU(2).", flush=True)
elif nin_unif >= 10:
    print(f"REFUTED on θ: E[u⁸] ≈ 35/256 (torus/CM).", flush=True)
else:
    print(f"INTERMEDIATE: neither full SU(2) nor torus.", flush=True)

out = {"primes": PRIMES, "seed": SEED, "R_sim": R_SIM,
       "SU2_Eu8": str(SU2_EU8), "UNIF_Eu8": str(UNIF_EU8),
       "results": [{k: (str(v) if isinstance(v, Fr) else v) for k, v in r.items()} for r in results],
       "aggregate": {"nin_su2": nin_su2, "nin_unif": nin_unif, "wdev_su2": wdev,
                     "small_L_dev": ms, "large_L_dev": ml, "intercept": icept}}
with open("/Users/trentpalelei/Desktop/Math Ex/.zcode/notes/btc_eig_lens/Eu8_results_v1.json", "w") as f:
    json.dump(out, f, indent=2)
print(f"\nwrote Eu8_results_v1.json", flush=True)
