#!/usr/bin/env python3
"""PREREG_ell_ge5_conditional_MI_v2 -- arms + controls with the two audit fixes.
  Tcond PRIMARY at ell>=11 (Icond = omnibus co-primary); C-cong via targeted Tcond with reported
  per-stratum N + Mc-cong+ planted positive.  Drill protocol: flicker (<0.00625) -> OOS retest.
Subcommands:
  insample : arms (ell=5,7,11,13, N~8000, seed 13) + C+/C- + C-cong(+plant)
  oos E .. : OOS retest (32-bit, N=12000, fresh seeds) for the listed ell
Number theory exact (build_arm); MI monotone vs exact permutation nulls."""
import sys, random
from math import gcd
import numpy as np
from ell_condmi_fast_v1 import Icond, Tcond, perm_Icond, perm_Tcond
exec(open('ell_mi_v3f.py').read().split('# ==== MACHINERY M0 ====')[0])

ALPHA = 0.05 / 8   # 0.00625
FLOOR = {  # measured R2 detectable-s (>=80%), per statistic and N; for the per-arm power gate
    8000:  {'Tcond': 0.06, 'Icond': 0.06},
    12000: {'Tcond': 0.03, 'Icond': 0.05},
}
def mediator_w(p, n, ell):
    return ((p - n) // ell) % ell   # (t-1)/ell mod ell, t-1 = p-n divisible by ell

def primary(ell):
    return 'Tcond' if ell >= 11 else 'both'

def crj_from_csr(csr, meta, ell):
    out = []
    for i, vpow in enumerate(csr):
        n = meta[i][2]; zn = pow(lpr(n), (n - 1) // ell, n); z = 1
        for r in range(ell):
            if z == vpow % n: out.append(r); break
            z = z * zn % n
        else: out.append(0)
    return np.array(out)

def run_arm(absD, ell, target, bits, seed, N_key, sh=20000, label=""):
    rnd = random.Random(seed)
    js, ks, csr, meta = build_arm(absD, ell, target, bits, rnd)
    j = np.array(js); k = np.array(ks); w = np.array([mediator_w(p, n, ell) for _, p, n in meta])
    pI = perm_Icond(j, k, w, ell, np.random.default_rng(seed), sh)[1]
    pT = perm_Tcond(j, k, w, ell, np.random.default_rng(seed + 1), sh)[1]
    crj = crj_from_csr(csr, meta, ell)
    pcrT = perm_Tcond(crj, k, w, ell, np.random.default_rng(seed + 2), sh)[1]
    prim = primary(ell)
    fl = FLOOR[N_key]
    tag = lambda p: ("FLICKER" if p < ALPHA else f"null (bound s>~{{}})")
    print(f"  [{label}] ell={ell} N={len(js)}  Tcond p={pT:.4f}{' *PRIMARY*' if prim!='both' else ''}"
          f"  Icond p={pI:.4f}  C-r(Tcond) p={pcrT:.4f}")
    print(f"        power floors: Tcond s~{fl['Tcond']}, Icond s~{fl['Icond']}  |  "
          f"primary={'Tcond' if prim=='Tcond' else 'Tcond&Icond'}  |  "
          f"{'FLICKER(s) -> OOS' if (pT<ALPHA or pI<ALPHA) else 'null'}")
    return {'ell': ell, 'N': len(js), 'pT': pT, 'pI': pI, 'pcrT': pcrT}

def build_ccong(meta, ell, rnd, limit=2500):
    # NOTE: t == 1 mod ell forced => U = |t-1| is ALWAYS divisible by ell.  So P == Q (mod U) already
    # forces P == Q (mod ell); to get both == 1 mod ell we draw rr == 1 (mod ell), coprime to U, and
    # walk by step = U (the mod-ell condition is subsumed, no CRT inverse needed).
    jj = []; kk = []; ww = []
    for U, p, n in meta[:limit]:
        if U < 2 * ell: continue
        w = mediator_w(p, n, ell)
        # rr coprime to U with rr == 1 mod ell
        rr = None
        for _ in range(200):
            c = rnd.randrange(1, U)
            c -= (c % ell) - 1          # snap to == 1 mod ell
            if c < 1: c += ell
            if c < U and gcd(c, U) == 1: rr = c; break
        if rr is None: continue
        step = U; found = []; v = rr; guard = 0
        while len(found) < 2 and guard < 6000:
            guard += 1
            if v > 3 and v % ell == 1 and is_prime(v, bases=(2, 3, 5, 7, 11, 13)) and U % v: found.append(v)
            v += step
        if len(found) == 2:
            P, Q = found
            zP = pow(lpr(P), (P - 1) // ell, P); zQ = pow(lpr(Q), (Q - 1) // ell, Q)
            jj.append(expo(U, P, ell, zP)); kk.append(expo(U, Q, ell, zQ)); ww.append(w)
    return np.array(jj), np.array(kk), np.array(ww)

def run_ccong(ell, seed=13):
    print(f"\n=== C-cong (R3 conditional, targeted Tcond) + Mc-cong+ planted positive, ell={ell} ===")
    rnd = random.Random(seed)
    _, _, _, meta = build_arm(3, ell, 8000, 30, rnd)
    j, k, w = build_ccong(meta, ell, rnd)
    if len(j) < 200:
        print(f"  C-cong short: N={len(j)}"); return
    perstrat = np.bincount(w, minlength=ell)
    pcc = perm_Tcond(j, k, w, ell, np.random.default_rng(70), 20000)[1]
    # Mc-cong+ : inject w-mediated shift on fraction s, must fire
    rng = np.random.default_rng(71); s = 0.12
    kp = k.copy(); m = rng.random(len(k)) < s
    kp[m] = (j[m] + w[m]) % ell
    ppl = perm_Tcond(j, kp, w, ell, np.random.default_rng(72), 20000)[1]
    print(f"  C-cong N={len(j)}  per-w-stratum N: min={perstrat.min()} median={int(np.median(perstrat))}"
          f"  (Tc cells = ell^2 = {ell*ell})")
    print(f"  natural C-cong Tcond p={pcc:.4f}   Mc-cong+ (plant s={s}) Tcond p={ppl:.4f}"
          f"  -> control {'FIRES (has power)' if ppl < 1e-3 else 'NO POWER at this N/s'}")

def run_insample():
    print("=== ARMS in-sample: D=-3, N~8000, 30-bit, seed 13 (same frozen sample) ===")
    res = [run_arm(3, ell, 8000, 30, 13, 8000, label="arm") for ell in (5, 7, 11, 13)]
    print("\n=== C+ / C- controls (ell=3) ===")
    run_arm(3, 3, 4000, 26, 12, 8000, label="C+ D=-3 KNOWN")
    run_arm(11, 3, 4000, 26, 12, 8000, label="C- D=-11 none")
    run_ccong(5)
    flick = [r['ell'] for r in res if r['pT'] < ALPHA or r['pI'] < ALPHA]
    print(f"\n>>> in-sample FLICKERS (need OOS): {flick if flick else 'NONE'}")

def run_oos(ells):
    print(f"=== OOS retest: 32-bit, N=12000, fresh seeds, ell={ells} ===")
    seeds = {5: 777333, 7: 424242, 11: 505011, 13: 606013}
    for ell in ells:
        run_arm(3, ell, 12000, 32, seeds.get(ell, 900 + ell), 12000, label="OOS")

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "insample"
    if cmd == "insample": run_insample()
    elif cmd == "oos": run_oos([int(x) for x in sys.argv[2:]])
    elif cmd == "ccong": run_ccong(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
