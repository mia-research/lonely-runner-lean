#!/usr/bin/env python3
"""Trust-but-verify the experiment-designer's two load-bearing catches before acting on them.
(a) point-4 identities: p == (t-1) mod n  and  n == -(t-1) mod p  on real CM instances.
(b) point-5 power split: at ell=11,13 is Icond under-powered vs Tcond for the uniform-shift bridge?
Synthetic + already-frozen sampler; no new inference on arm j;k association."""
import random
import numpy as np
from ell_condmi_fast_v1 import Icond, Tcond, perm_Icond, perm_Tcond
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])

# ---- (a) verify the identities on real instances ----
print("=== (a) common-U identities on real D=-3 instances ===")
for ell in (5, 13):
    rnd = random.Random(13)
    js, ks, csr, meta = build_arm(3, ell, 300, 30, rnd)
    ok1 = ok2 = okt = True
    for U, p, n in meta:
        t = p + 1 - n
        ok1 &= (p % n) == ((t - 1) % n)
        ok2 &= (n % p) == ((-(t - 1)) % p)
        okt &= (t % ell) == 1               # forced degeneracy
    print(f"  ell={ell} N={len(meta)}:  p==(t-1) mod n:{ok1}   n==-(t-1) mod p:{ok2}   t==1 mod ell:{okt}")

# ---- (b) power split Icond vs Tcond for uniform-shift bridge, N=12000 ----
print("\n=== (b) uniform-shift injection power, N=12000, R=20, sh=1000, detect p<0.00625 ===")
print(f"  {'ell':>3} {'s':>5} {'Icond hit%':>11} {'Tcond hit%':>11}")
ALPHA = 0.05 / 8
for ell in (11, 13):
    for s in (0.0, 0.02, 0.03, 0.04, 0.06):
        rng = np.random.default_rng(2000 + ell)
        hi = ht = 0; R = 20; N = 12000
        for _ in range(R):
            w = rng.integers(0, ell, N); k = rng.integers(0, ell, N)
            copy = rng.random(N) < s
            j = np.where(copy, (k + w) % ell, rng.integers(0, ell, N))
            hi += (perm_Icond(j, k, w, ell, rng, 1000)[1] < ALPHA)
            ht += (perm_Tcond(j, k, w, ell, rng, 1000)[1] < ALPHA)
        print(f"  {ell:>3} {s:>5.2f} {100*hi/R:>10.0f}% {100*ht/R:>10.0f}%")
