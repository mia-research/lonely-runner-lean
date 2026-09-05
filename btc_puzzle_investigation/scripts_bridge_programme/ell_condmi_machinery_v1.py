#!/usr/bin/env python3
"""PREREG_ell_ge5_conditional_MI_v1 -- MACHINERY controls only (M0, Mc+, Mc-).
Tests the conditional statistic on SYNTHETIC data; does NOT touch the frozen arms.
Safe to run before the experiment-designer sign-off (it exercises the instrument, not the data).
Exact integers for labels; MI is a monotone statistic vs exact permutation nulls."""
from math import log
from collections import Counter, defaultdict
import random

# ---------- statistics ----------
def MI(js, ks):                      # marginal MI (used only to demonstrate BLINDNESS)
    N = len(js); j = Counter(js); k = Counter(ks); jt = Counter(zip(js, ks)); I = 0.0
    for (a, b), c in jt.items():
        I += (c/N) * log((c/N) / ((j[a]/N) * (k[b]/N)))
    return I

def Icond(js, ks, ws):               # PRIMARY: stratified conditional MI  I(j;k|w)
    N = len(js); strat = defaultdict(list)
    for a, b, w in zip(js, ks, ws): strat[w].append((a, b))
    tot = 0.0
    for w, lst in strat.items():
        Nw = len(lst)
        if Nw < 2: continue
        jj = Counter(a for a, b in lst); kk = Counter(b for a, b in lst); jt = Counter(lst)
        mi = 0.0
        for (a, b), c in jt.items():
            mi += (c/Nw) * log((c/Nw) / ((jj[a]/Nw) * (kk[b]/Nw)))
        tot += (Nw/N) * mi
    return tot

def _Idw(ds, ws):                    # MI between a shift residual d and the mediator w
    N = len(ds); dd = Counter(ds); ww = Counter(ws); jt = Counter(zip(ds, ws)); I = 0.0
    for (a, b), c in jt.items():
        I += (c/N) * log((c/N) / ((dd[a]/N) * (ww[b]/N)))
    return I

def Tcond(js, ks, ws, ell):          # CO-PRIMARY: max over choice-free alignments of I(j-b k ; w)
    best = 0.0
    for b in range(1, ell):
        ds = [(x - b*y) % ell for x, y in zip(js, ks)]
        v = _Idw(ds, ws)
        if v > best: best = v
    return best

# ---------- nulls (one per statistic; see prereg s2) ----------
def perm_Icond(js, ks, ws, rnd, sh):     # within-stratum shuffle of k
    obs = Icond(js, ks, ws)
    idx = defaultdict(list)
    for i, w in enumerate(ws): idx[w].append(i)
    ks = list(ks); ge = 0
    for _ in range(sh):
        kl = list(ks)
        for w, ii in idx.items():
            vals = [kl[i] for i in ii]; rnd.shuffle(vals)
            for i, v in zip(ii, vals): kl[i] = v
        if Icond(js, kl, ws) >= obs - 1e-12: ge += 1
    return obs, (ge + 1) / (sh + 1)

def perm_Tcond(js, ks, ws, ell, rnd, sh):  # shuffle the w-labels
    obs = Tcond(js, ks, ws, ell)
    wl = list(ws); ge = 0
    for _ in range(sh):
        rnd.shuffle(wl)
        if Tcond(js, ks, wl, ell) >= obs - 1e-12: ge += 1
    return obs, (ge + 1) / (sh + 1)

def perm_MI(js, ks, rnd, sh):            # marginal null (shuffle k) -- to show blindness
    obs = MI(js, ks); kl = list(ks); ge = 0
    for _ in range(sh):
        rnd.shuffle(kl)
        if MI(js, kl) >= obs - 1e-12: ge += 1
    return obs, (ge + 1) / (sh + 1)

# ================= M0: choice-freeness =================
print("=== M0: Icond + Tcond invariant under UNIT relabelings j->a j, k->c k (w untouched) ===")
rnd = random.Random(10); ell = 7; N = 3000
ws = [rnd.randrange(ell) for _ in range(N)]
ks = [rnd.randrange(ell) for _ in range(N)]
js = [(k + ws[i] + rnd.randrange(2)) % ell for i, k in enumerate(ks)]   # some j;k|w structure
i0 = Icond(js, ks, ws); t0 = Tcond(js, ks, ws, ell); oki = okt = True
for a, c in ((2, 3), (3, 5), (6, 4)):   # units mod 7
    j2 = [(a*x) % ell for x in js]; k2 = [(c*x) % ell for x in ks]
    oki &= abs(Icond(j2, k2, ws) - i0) < 1e-12
    okt &= abs(Tcond(j2, k2, ws, ell) - t0) < 1e-12
print(f"  Icond choice-free: {oki}   Tcond choice-free: {okt}   (Icond={i0:.6f}, Tcond={t0:.6f})")

# ================= Mc+ : the load-bearing synthetic-positive =================
# j = (k + w) mod ell, w,k indep uniform.  Marginally j _|_ k (marginal MI blind);
# conditionally j=k+w within each stratum -> Icond, Tcond must FIRE.
print("\n=== Mc+ : uniform-shift bridge  j=(k+w) mod ell  (marginal-blind, conditional-visible) ===")
print(f"  {'ell':>3} {'marg MI p':>10} {'Icond p':>9} {'Tcond p':>9}   (marg should be ~1; cond should be tiny)")
for ell in (5, 7, 11, 13):
    rnd = random.Random(100 + ell); N = 6000
    ws = [rnd.randrange(ell) for _ in range(N)]
    ks = [rnd.randrange(ell) for _ in range(N)]
    js = [(k + ws[i]) % ell for i, k in enumerate(ks)]
    _, pm = perm_MI(js, ks, rnd, 3000)
    _, pi = perm_Icond(js, ks, ws, rnd, 3000)
    _, pt = perm_Tcond(js, ks, ws, ell, rnd, 3000)
    print(f"  {ell:>3} {pm:>10.4f} {pi:>9.4f} {pt:>9.4f}")

# ================= Mc- : synthetic null =================
print("\n=== Mc- : j,k,w all independent uniform  ->  conditional stats null ===")
print(f"  {'ell':>3} {'Icond p':>9} {'Tcond p':>9}   (both should be large)")
for ell in (5, 7, 11, 13):
    rnd = random.Random(500 + ell); N = 6000
    ws = [rnd.randrange(ell) for _ in range(N)]
    ks = [rnd.randrange(ell) for _ in range(N)]
    js = [rnd.randrange(ell) for _ in range(N)]
    _, pi = perm_Icond(js, ks, ws, rnd, 3000)
    _, pt = perm_Tcond(js, ks, ws, ell, rnd, 3000)
    print(f"  {ell:>3} {pi:>9.4f} {pt:>9.4f}")
