#!/usr/bin/env python3
"""Audit the two borderline 'SIGNAL' flags from angular_interference_scaling_v1:
   gen130 chi2(Y) vs d%2, and (chi6(Y) vs bit_mid).  A real leak plateaus (I_c
   flat, z grows ~sqrt(M)) and REPRODUCES across independent seeds.  Noise does not."""
import numpy as np
from angular_interference_scaling_v1 import gen_keys, chi2, chi6, conditional, loglog_slope
Ms = [2000, 5000, 10000, 20000, 40000]

def probe(bitlen, seed, angle_fn, tname, tfn, Bnull=400):
    d, X, Y = gen_keys(bitlen, 40000, seed)
    coord = Y  # both flagged angles are on Y
    feat = np.array([angle_fn(v) if angle_fn(v) is not None else 0 for v in coord], dtype=np.int64)
    targ = np.array([tfn(v) for v in d], dtype=np.int64)
    rng = np.random.default_rng(999)
    res = conditional(feat, targ, Ms, Bnull, rng)
    Ic = [r[1] for r in res]; z = [r[2] for r in res]
    s_mi = loglog_slope(Ms, Ic)
    s_z = float(np.polyfit(np.sqrt(np.array(Ms, float)), np.array(z, float), 1)[0])  # noqa: float
    print(f"  b{bitlen} seed{seed} {tname:9}: "
          + " ".join(f"z={zz:+.2f}" for zz in z)
          + f"  | loglogslope(I_c)={s_mi:+.2f} z/sqrtM={s_z:+.4f}")

print("=== AUDIT 1: chi2(Y) vs d%2  (gen130 flagged z=3.66) ===")
for seed in (11, 101, 202):
    probe(130, seed, chi2, "d%2", lambda v: v % 2)
print("  reference gen256 (was noise z=1.24):")
for seed in (7, 303):
    probe(256, seed, chi2, "d%2", lambda v: v % 2)

print("\n=== AUDIT 2: chi6(Y) vs bit_mid  (d100k flagged z=3.06) ===")
def bit_mid(v): return (v >> (v.bit_length() // 2)) & 1
for seed in (11, 101):
    probe(130, seed, chi6, "bit_mid", bit_mid)
for seed in (7, 303):
    probe(256, seed, chi6, "bit_mid", bit_mid)

print("\nExpected if REAL: z rises with M (z/sqrtM>0 clearly) AND loglogslope~0 AND")
print("reproduces across seeds. If NOISE: z wanders, no consistent sign across seeds.")
