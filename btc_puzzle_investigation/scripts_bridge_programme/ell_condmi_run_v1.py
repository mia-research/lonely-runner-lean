#!/usr/bin/env python3
"""PREREG_ell_ge5_conditional_MI_v1 -- full run harness.
  arg 'r2'   : R2 injection-power (SYNTHETIC, pre-approval-safe) -- run now.
  arg 'arms' : the frozen-data arms + data controls (C+, C-, C-cong, C-r) -- GATED on
               experiment-designer sign-off; do NOT run before approval.
Number theory exact (build_arm from ell_mi_v3f.py); MI monotone vs exact permutation nulls."""
import sys, random
import numpy as np
from ell_condmi_fast_v1 import Icond, Tcond, MI, perm_Icond, perm_Tcond, perm_MI

# reuse the exact, audited sampler + symbol code (strip its auto-run M0/arms tail)
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])

ALPHA = 0.05 / 8   # Bonferroni over 4 arms x 2 stats = 0.00625

def mediator_w(p, n, ell):
    """w = ((t-1)/ell) mod ell, t-1 = p-n (exactly divisible by ell since p==n==1 mod ell)."""
    return ((p - n) // ell) % ell

# ---------------- R2 : injection power (synthetic; s=0 is the null) ----------------
def run_r2():
    print("=== R2: conditional-shift injection power. j:=(k+w) w.p. s else uniform; s=0 = NULL. N=8000 ===")
    print(f"  detected := permutation p < ALPHA={ALPHA:.5f} in >=80% of R=15 reps")
    print(f"  {'ell':>3} {'Icond floor':>12} {'Tcond floor':>12}   (smallest injected s at >=80% power; NULL s=0 must not fire)")
    rng = np.random.default_rng(11); N = 8000
    for ell in (5, 7, 11, 13):
        out = {}
        for stat, nm in (('I', 'Icond'), ('T', 'Tcond')):
            floor = ">0.15"
            for s in (0.0, 0.03, 0.06, 0.10, 0.15):
                hits = 0; Rr = 15
                for _ in range(Rr):
                    w = rng.integers(0, ell, N); k = rng.integers(0, ell, N)
                    copy = rng.random(N) < s
                    j = np.where(copy, (k + w) % ell, rng.integers(0, ell, N))
                    if stat == 'I':
                        pv = perm_Icond(j, k, w, ell, rng, 300)[1]
                    else:
                        pv = perm_Tcond(j, k, w, ell, rng, 300)[1]
                    hits += (pv < ALPHA)
                if s == 0.0:
                    if hits / Rr > 0.2:
                        floor = f"NULL FIRES {hits}/{Rr}"; break
                    continue
                if hits / Rr >= 0.8:
                    floor = s; break
            out[nm] = floor
        print(f"  {ell:>3} {str(out['Icond']):>12} {str(out['Tcond']):>12}")
        sys.stdout.flush()

# ---------------- ARMS + data controls (GATED) ----------------
def cong_symbols(meta, ell, rnd):
    """C-cong (R3 conditional): two indep primes P=Q (mod U), both =1 mod ell; symbols of the SAME U,
    stratified by the SAME w.  Returns j',k',w' arrays."""
    from math import gcd
    jj = []; kk = []; ww = []
    for U, p, n in meta:
        if U < 2 or U % ell == 0: continue
        w = mediator_w(p, n, ell)
        rr = rnd.randrange(1, U)
        while gcd(rr, U) > 1: rr = rnd.randrange(1, U)
        inv = pow(U % ell, -1, ell); x0 = rr + U * (((1 - rr) * inv) % ell); step = U * ell
        found = []; v = x0; guard = 0
        while len(found) < 2 and guard < 4000:
            guard += 1
            if v > 3 and is_prime(v, bases=(2, 3, 5, 7, 11, 13)) and U % v: found.append(v)
            v += step
        if len(found) == 2:
            P, Q = found
            zP = pow(lpr(P), (P - 1) // ell, P); zQ = pow(lpr(Q), (Q - 1) // ell, Q)
            jj.append(expo(U, P, ell, zP)); kk.append(expo(U, Q, ell, zQ)); ww.append(w)
    return np.array(jj), np.array(kk), np.array(ww)

def run_one(absD, ell, target, bits, seed, sh=20000, label=""):
    rnd = random.Random(seed)
    js, ks, csr, meta = build_arm(absD, ell, target, bits, rnd)
    j = np.array(js); k = np.array(ks); w = np.array([mediator_w(p, n, ell) for _, p, n in meta])
    _, pi = perm_Icond(j, k, w, ell, rnd_np(seed), sh)
    _, pt = perm_Tcond(j, k, w, ell, rnd_np(seed + 1), sh)
    # C-r random base, stratified by same w
    crj = []
    for i, vpow in enumerate(csr):
        n = meta[i][2]; zn = pow(lpr(n), (n - 1) // ell, n); z = 1
        for r in range(ell):
            if z == vpow % n: crj.append(r); break
            z = z * zn % n
        else: crj.append(0)
    crj = np.array(crj)
    _, pcr = perm_Icond(crj, k, w, ell, rnd_np(seed + 2), sh)
    print(f"  [{label}] ell={ell} N={len(js)}  Icond p={pi:.4f}  Tcond p={pt:.4f}  C-r Icond p={pcr:.4f}")
    return pi, pt

def rnd_np(seed): return np.random.default_rng(seed)

def run_arms():
    print("=== ARMS: ell in {5,7,11,13}, D=-3, in-sample N~8000 seed 13 (same frozen sample) ===")
    for ell in (5, 7, 11, 13):
        run_one(3, ell, 8000, 30, 13, label="arm")
    print("\n=== C+ / C- (ell=3) ===")
    run_one(3, 3, 4000, 26, 12, label="C+ D=-3 bridge KNOWN")
    run_one(11, 3, 4000, 26, 12, label="C- D=-11 no bridge")
    print("\n=== C-cong (R3 conditional, ell=5) ===")
    rnd = random.Random(13)
    _, _, _, meta = build_arm(3, 5, 8000, 30, rnd)
    ccj, cck, ccw = cong_symbols(meta[:1500], 5, rnd)
    if len(ccj) >= 200:
        _, pcc = perm_Icond(ccj, cck, ccw, 5, rnd_np(77), 20000)
        print(f"  C-cong ell=5 N={len(ccj)}  Icond p={pcc:.4f}")
    else:
        print(f"  C-cong short: N={len(ccj)}")

if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "r2"
    if what == "r2": run_r2()
    elif what == "arms": run_arms()
