#!/usr/bin/env python3
"""
kden_h3_spectral_v1.py -- H3 (spectral arm) of PREREG_kden_ramanujan_comb_v1.md, sections 2.5/2.6/3/4.2.

BRANCH A applies: H2b confirmed exactly (0 mismatches, 8/8 configs), so per section 7 this arm is
CHARACTERIZATION ONLY -- no p from it is independent evidence.  Per section 0.3 F-1 the
"exact-geometry predicted spectrum vs observed spectrum" correlation is FORCED (rho=1) and is NOT
computed here.  What is tested is the EQUAL-WIDTH Ramanujan factorization, which HYP-G does not force.

Models built from the PREDICTED geometry only:
   W(w,f)  = sin(pi f w / A) / (pi f / A)                  Dirichlet kernel of a width-w window
   c_q(f)  = mu(q/g) phi(q) / phi(q/g),  g = gcd(q,f)      Ramanujan sum
   RAM(f)  = | sum_q q * W(wbar_q,f) * c_q(f) |^2          coherent (comb) model
   FLAT(f) = sum_q q^2 * W(wbar_q,f)^2 * phi(q)            incoherent (random-centre) model
   R2_ram  = 1 - SSE(log P_obs - log RAM - c) / SST(log P_obs)      c = single additive (scale) constant

Null-1 (PRIMARY matched null) = run-block cyclic permutation: preserves the value multiset, the
run-length multiset, their pairing, piecewise-constancy and r_q; destroys only the Farey PLACEMENT.
Cyclic rotation is BANNED (|FFT|-invariant, zero power -- section 0.3 F-3).

Named float carve-out (section 8): FFT/log/sin/R2 only; every decision is an integer permutation rank.
"""
import sys, hashlib
from fractions import Fraction
from math import gcd, pi, sin, log
import numpy as np
from kden_ramanujan_comb_v1 import (predict_levelsets, k_den_sequence, phi, CONFIGS)

ALPHA_NUM, ALPHA_DEN = 1, 60
B_DRAWS = 999


def mobius(n):
    r, m, cnt = 1, n, 0
    d = 2
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            cnt += 1
        d += 1
    if m > 1:
        cnt += 1
    return -1 if cnt % 2 else 1


def ramanujan(q, f):
    g = gcd(q, f)
    return mobius(q // g) * phi(q) // phi(q // g)


def widths(rows, M):
    """wbar_q = mean predicted width (in integer offsets) of the q-intervals.  Exact Fraction."""
    acc, cnt = {}, {}
    for (q, j, lo, hi, n, fl) in rows:
        acc[q] = acc.get(q, 0) + n
        cnt[q] = cnt.get(q, 0) + 1
    return {q: Fraction(acc[q], cnt[q]) for q in acc}


def models(A, M, wbar, F_max, qs=None):
    qs = qs if qs is not None else sorted(wbar)
    f = np.arange(1, F_max + 1, dtype=float)
    RAM = np.zeros(F_max)
    FLAT = np.zeros(F_max)
    coh = np.zeros(F_max)
    for q in qs:
        w = float(wbar[q])
        Wk = np.sin(pi * f * w / A) / (pi * f / A)
        cq = np.array([ramanujan(q, int(ff)) for ff in f], dtype=float)
        coh += q * Wk * cq
        FLAT += (q ** 2) * (Wk ** 2) * phi(q)
    RAM = coh ** 2
    return RAM, FLAT


def power_spectrum(seq, F_max):
    x = np.asarray(seq, dtype=float)
    x = x - x.mean()
    P = np.abs(np.fft.rfft(x)) ** 2
    return P[1:F_max + 1]


def r2(logobs, model):
    lm = np.log(np.maximum(model, 1e-300))
    d = logobs - lm
    c = d.mean()
    sse = float(((d - c) ** 2).sum())
    sst = float(((logobs - logobs.mean()) ** 2).sum())
    return 1.0 - sse / sst if sst > 0 else 0.0


def circ_runs(seq):
    A = len(seq)
    starts = [i for i in range(A) if seq[i] != seq[(i - 1) % A]]
    if not starts:
        return [(seq[0], A)]
    out = []
    for k, s in enumerate(starts):
        e = starts[(k + 1) % len(starts)]
        ln = (e - s) % A or A
        out.append((seq[s], ln))
    return out


def null1(runs, rng):
    """Run-block cyclic permutation: permute run ORDER, concatenate."""
    idx = rng.permutation(len(runs))
    out = np.empty(sum(r[1] for r in runs), dtype=np.int64)
    pos = 0
    for i in idx:
        v, ln = runs[i]
        out[pos:pos + ln] = v
        pos += ln
    return out


def run_config(cid, bexp, M, rng, verbose=True):
    A = 1 << (bexp - 1)
    F_max = min(2 * M * M, A // 2)
    rows, assign, boundary = predict_levelsets(A, M)
    wbar = widths(rows, M)
    RAM, FLAT = models(A, M, wbar, F_max)

    # --- ordering: TOP3_pred emitted + hashed BEFORE P_obs exists
    top3 = list(np.argsort(RAM)[-3:][::-1] + 1)
    h = hashlib.sha256(("%s|%s" % (cid, top3)).encode()).hexdigest()[:16]

    seq = k_den_sequence(A, M)
    P = power_spectrum(seq, F_max)
    logP = np.log(np.maximum(P, 1e-300))
    R_ram, R_flat = r2(logP, RAM), r2(logP, FLAT)

    # H3-top: argmax of P_obs / (null floor); use the Null-1 mean spectrum as the floor
    runs = circ_runs(seq)
    floor = np.zeros(F_max)
    for _ in range(20):
        floor += power_spectrum(null1(runs, rng), F_max)
    floor /= 20
    top_obs = int(np.argmax(P / np.maximum(floor, 1e-300)) + 1)

    # H3-HC: highly-composite-wrt-M decile
    DM = np.array([sum(phi(q) for q in range(1, M + 1) if ff % q == 0) for ff in range(1, F_max + 1)])
    thr = np.quantile(DM, 0.9)
    hc = DM >= thr
    d_hc = float(logP[hc].mean() - logP[~hc].mean()) if hc.any() and (~hc).any() else 0.0

    if verbose:
        print("\n== %s bexp=%d A=%d M=%d F_max=%d ==" % (cid, bexp, A, M, F_max))
        print("   TOP3_pred=%s (sha %s)   observed top |f| = %d   %s"
              % (top3, h, top_obs, "HIT" if top_obs in top3 else "miss"))
        print("   R2_ram = %+.4f   R2_flat = %+.4f   dR2 = %+.4f   Delta_HC = %+.4f"
              % (R_ram, R_flat, R_ram - R_flat, d_hc))
    return dict(cid=cid, A=A, M=M, F_max=F_max, RAM=RAM, FLAT=FLAT, seq=seq, runs=runs,
                R_ram=R_ram, R_flat=R_flat, top3=top3, top_obs=top_obs, d_hc=d_hc, wbar=wbar)


def main():
    rng = np.random.default_rng(20260723)
    print("=" * 90)
    print("H3 SPECTRAL ARM -- CHARACTERIZATION ONLY (Branch A: H2b confirmed).  B=%d alpha*=1/60" % B_DRAWS)
    print("=" * 90)

    res = [run_config(cid, bexp, M, rng) for cid, bexp, M in CONFIGS]
    S_obs = sum(r['R_ram'] for r in res)
    hits = sum(1 for r in res if r['top_obs'] in r['top3'])

    # ---- joint Null-1 for S_ram
    print("\n--- joint Null-1 (%d draws) ---" % B_DRAWS)
    rk = 0
    rk_hc = 0
    d_hc_obs = sum(r['d_hc'] for r in res)
    for b in range(B_DRAWS):
        s = 0.0
        dh = 0.0
        for r in res:
            ns = null1(r['runs'], rng)
            P = power_spectrum(ns, r['F_max'])
            lp = np.log(np.maximum(P, 1e-300))
            s += r2(lp, r['RAM'])
            M_, F_ = r['M'], r['F_max']
            DM = np.array([sum(phi(q) for q in range(1, M_ + 1) if ff % q == 0) for ff in range(1, F_ + 1)])
            hc = DM >= np.quantile(DM, 0.9)
            dh += float(lp[hc].mean() - lp[~hc].mean())
        if s >= S_obs:
            rk += 1
        if dh >= d_hc_obs:
            rk_hc += 1
    def fires(r):
        return (1 + r) * ALPHA_DEN <= ALPHA_NUM * (B_DRAWS + 1)
    print("  S_ram  = %+.4f   rank=%d/%d  -> %s" % (S_obs, rk, B_DRAWS, "FIRES" if fires(rk) else "null"))
    print("  Delta_HC pooled = %+.4f  rank=%d/%d -> %s" % (d_hc_obs, rk_hc, B_DRAWS, "FIRES" if fires(rk_hc) else "null"))
    print("  H3-top hits = %d/8" % hits)

    # ---- PC-comb (must fire) on each config: synthetic comb from Q_plant={7,11,13}
    print("\n--- PC-comb (planted comb, Q_plant={7,11,13}) ---")
    Qp = [7, 11, 13]
    for r in res[:3] + res[4:6]:
        A, F_max = r['A'], r['F_max']
        w = max(2, A // 400)
        synth = np.zeros(A, dtype=np.int64)
        for q in Qp:
            for j in range(q):
                if gcd(j, q) != 1:
                    continue
                c = j * A // q
                for t in range(-w // 2, w // 2 + 1):
                    synth[(c + t) % A] = q
        wb = {q: Fraction(w) for q in Qp}
        RAMp, _ = models(A, r['M'], wb, F_max, qs=Qp)
        P = power_spectrum(synth, F_max)
        R = r2(np.log(np.maximum(P, 1e-300)), RAMp)
        runs = circ_runs(list(synth))
        nr = 0
        for _ in range(199):
            ns = null1(runs, rng)
            Pn = power_spectrum(ns, F_max)
            if r2(np.log(np.maximum(Pn, 1e-300)), RAMp) >= R:
                nr += 1
        ok = R >= 0.80 and (1 + nr) * ALPHA_DEN <= ALPHA_NUM * 200
        print("  %s  R2_ram(synthetic) = %+.4f  null rank=%d/199  -> %s"
              % (r['cid'], R, nr, "FIRES" if ok else "*** did NOT meet R2>=0.80 & p<=1/60 ***"))

    # ---- H3-resid: which q-sub-family carries the residual
    print("\n--- H3-resid (residual log P_obs - log RAM against q-sub-families) ---")
    for r in res[:4]:
        A, M, F_max = r['A'], r['M'], r['F_max']
        P = power_spectrum(r['seq'], F_max)
        lp = np.log(np.maximum(P, 1e-300))
        base = lp - np.log(np.maximum(r['RAM'], 1e-300))
        base = base - base.mean()
        line = "  %s:" % r['cid']
        for name, sel in (("odd", lambda q: q % 2 == 1), ("q|A", lambda q: A % q == 0),
                          ("prime", lambda q: q > 1 and all(q % d for d in range(2, int(q ** 0.5) + 1))),
                          ("sqfree", lambda q: mobius(q) != 0)):
            qs = [q for q in sorted(r['wbar']) if sel(q)]
            if not qs:
                continue
            RA, _ = models(A, M, r['wbar'], F_max, qs=qs)
            la = np.log(np.maximum(RA, 1e-300)); la = la - la.mean()
            rho = float(np.dot(base, la) / (np.linalg.norm(base) * np.linalg.norm(la) + 1e-30))
            line += "  %s rho=%+.3f" % (name, rho)
        print(line)
    print("H3_DONE")


if __name__ == '__main__':
    main()
