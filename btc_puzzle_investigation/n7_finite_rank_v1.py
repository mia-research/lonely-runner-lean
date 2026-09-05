#!/usr/bin/env python3
"""N7 finite-rank carrier probe — executes PREREG_n7_finite_rank_carrier_v1.md.

HYPOTHESIS: the char's U(b,c) is a sum of r<=4 Weil numbers of modulus sqrt(p) (record P6a/P6b:
|U| <= (1+ord_O(f))sqrt(p)+1, r=4 for c!=0 and r=3 for c=0), while the Hermitian null is a sum of
n~p random phases -> Gaussian -> Rayleigh. A finite-r walk has EXCESS near-zero mass and a hard
ceiling at matched 2nd moment -- exactly the measured signature.

Signal path reuses the FROZEN instrument's exact-int EC arithmetic (subrayleigh_deficit_scaling_v1).
Float: the p x p FFT and the MC walk are the sanctioned carve-out (that prereg's §8); every
comparison is a ranked/CDF statistic, never a discrete decision.  # noqa: float — (stat) FFT carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; all statistics are CDF distances on exact-int-derived point sets
"""
import sys, time, json
import numpy as np
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import subrayleigh_deficit_scaling_v1 as inst

TAUS = [0.05, 0.10, 0.20, 0.30, 0.50]  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
RANKS = [2, 3, 4, 5, 6, 8, 12]
MCN = 4_000_000

def aU_of(pts, g, p):
    W = np.zeros((p, p), dtype=np.complex128)
    xs = np.fromiter((x for x, _ in pts), dtype=np.int64, count=len(pts))
    ys = np.fromiter((y for _, y in pts), dtype=np.int64, count=len(pts))
    np.add.at(W, (xs, ys), g)
    return np.abs(np.fft.fft2(W))  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision

def tail(rho, taus=TAUS):
    """P(rho < tau) with rho normalised so E[rho^2] = 1."""
    r = rho / np.sqrt((rho * rho).mean())  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
    return np.array([float((r < t).mean()) for t in taus])  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision

def walk_tail(r, rng, N=MCN):
    """Low-tail CDF of |sum of r unit phases| normalised to E[.^2]=1 (=> divide by sqrt(r))."""
    th = rng.uniform(0, 2 * np.pi, size=(N, r))
    z = np.exp(1j * th).sum(axis=1) / np.sqrt(r)  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
    a = np.abs(z)  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
    return np.array([float((a < t).mean()) for t in TAUS])  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision

def rayleigh_tail():
    return np.array([1 - np.exp(-t * t) for t in TAUS])  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision

def fit_r(obs, table):
    """r minimising squared CDF distance on the low tail (first 3 taus)."""
    best, bd = None, None
    for r, tv in table.items():
        d = float(((obs[:3] - tv[:3]) ** 2).sum())  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
        if bd is None or d < bd: best, bd = r, d
    return best, bd

if __name__ == "__main__":
    rng = np.random.default_rng(20260902)
    print("building finite-rank reference table (MC, %d draws/rank)" % MCN, flush=True)
    table = {r: walk_tail(r, rng) for r in RANKS}
    ray = rayleigh_tail()
    print(f"  taus            {['%.2f'%t for t in TAUS]}")
    print(f"  Rayleigh        {np.round(ray,5)}")
    for r in RANKS:
        print(f"  r={r:<2d} walk       {np.round(table[r],5)}", flush=True)

    out = {}
    for p in (349, 577, 991, 2089):
        t0 = time.time()
        n = inst.curve_order(p) if hasattr(inst, "curve_order") else None
        if n is None:
            n = 1 + sum(1 for x in range(p)
                        for _ in range(1 + inst_legendre(p, x))) if False else None
        # use the instrument's own order routine
        n = inst.group_order(p) if hasattr(inst, "group_order") else n
        if n is None:
            # fall back: count points directly (exact int)
            cnt = 1
            for x in range(p):
                r_ = (x * x % p * x + 7) % p
                if r_ == 0: cnt += 1
                elif pow(r_, (p - 1) // 2, p) == 1: cnt += 2
            n = cnt
        G, pts = inst.all_points(p, n)
        K = 30 if p < 1000 else 10
        gch = inst.char_weight(n)
        A = aU_of(pts, gch, p)
        strata = {"bulk": A[1:, 1:].ravel(), "c0_xonly": A[:, 0][1:], "b0_yonly": A[0, :][1:]}
        nullstr = {k: [] for k in strata}
        for k_ in range(K):
            gn = inst.null_weight(pts, n, seed=p * 10 ** 6 + k_)
            B = aU_of(pts, gn, p)
            nullstr["bulk"].append(B[1:, 1:].ravel())
            nullstr["c0_xonly"].append(B[:, 0][1:])
            nullstr["b0_yonly"].append(B[0, :][1:])
        row = {"p": p, "n": n, "K": K}
        print(f"\np={p} n={n} K={K}  [{time.time()-t0:.0f}s]", flush=True)
        for k in strata:
            oc = tail(strata[k]); on = tail(np.concatenate(nullstr[k]))
            rc, dc = fit_r(oc, table); rn, dn = fit_r(on, table)
            exc = [(oc[i] / on[i] - 1) * 100 if on[i] > 0 else float("nan") for i in range(3)]  # noqa: float — (stat) sanctioned FFT/MC carve-out per PREREG_subrayleigh_deficit_scaling_v1 §8; point set is exact-int EC arithmetic upstream, every statistic is a ranked CDF distance, no discrete/algebraic decision
            row[k] = {"char_tail": oc.tolist(), "null_tail": on.tolist(),
                      "r_char": rc, "r_null": rn, "excess_pct": exc}
            print(f"  {k:<10} char {np.round(oc,5)}  r_hat={rc}", flush=True)
            print(f"  {'':<10} null {np.round(on,5)}  r_hat={rn}   "
                  f"near-zero excess char-vs-null @tau=.05/.10/.20: "
                  f"{exc[0]:+.1f}% / {exc[1]:+.1f}% / {exc[2]:+.1f}%", flush=True)
        out[p] = row
        json.dump(out, open("n7_finite_rank_v1.json", "w"), indent=1)
    print("\ndumped n7_finite_rank_v1.json", flush=True)
