#!/usr/bin/env python3
"""
ct_boundary_stratified_v1.py — ARM A2: the IDEA behind proposal 2, not its method.

Arm A (ct_event_complete_v1.py) ports the METHOD (event-complete instead of
sampled) and buys ~5-30x power on the same question "is there a coupling".
This script tests the IDEA, which is a different and stronger claim:

    "The rounding process in the Eisenstein lift is a Diophantine approximation
     threshold.  Define the exact geometric boundary equations of the sextants;
     the scalars d that trigger the C_T carry-leak will form a rigid, determinable
     sequence of bounds -- exactly like the bad intervals in the LRC coupling
     principle.  This transforms the 2% noise into a precise list."

The idea's content is LOCALISATION: the departure from the tensor law is not a
diffuse coupling parameter, it is a DETERMINISTIC EVENT that fires when the lift
sum lands near an exact decision boundary.  That is decidable.

THE EXACT BOUNDARY.  With reduced basis (R1,R2), DET = det(R1,R2), the carry of
s = z_1 + z_2 is c_i = rdiv(N_i, DET) where
        N_1 = s_x R2_y - s_y R2_x ,      N_2 = -s_x R1_y + s_y R1_x .
The decision boundary is exactly  a_i := N_i/DET  in  Z + 1/2 .  Define the exact
integer MARGIN numerator
        M_i = DET - 2*|N_i - c_i*DET|   in [0, DET],     M = min(M_1, M_2).
M = 0 means the pair sits ON a boundary; M = DET means maximally interior.
All integers; no float anywhere in this path.

THE TEST.  Stratify the n^2 event-complete transitions by M (quantile bins over
the exact integer margins), and compute, WITHIN each stratum, the pooled G^2 for
the tensor factorisation "given the source state, are the two next-coordinates
independent?".  G^2 is computed from that stratum's own marginals, so a stratum
having a different state mix does not by itself create excess.

PRE-COMMITTED READING (frozen before any real curve is read):
  * IDEA SUPPORTED if the factorisation excess CONCENTRATES at low margin:
    G^2/df in the lowest-margin bin exceeds that in the highest-margin bin, and
    the margin-permutation control does NOT reproduce the gradient.  Then the
    departure is a boundary event, it is localised, and the object to build next
    is the explicit boundary set.
  * IDEA NOT SUPPORTED if G^2/df is flat in M (whatever its absolute level):
    the departure, if any, is not boundary-localised, and "a rigid determinable
    sequence of scalars" has no support at this scope.  This bounds a
    LOCALISATION, and is not a statement that the coupling is zero.
  * VOID if the controls do not fire.

CONTROLS (both must fire or the arm is void):
  K1  margin permutation: permute the margin labels across transitions, keeping
      every state count and every transition identical.  This destroys any
      margin-deviation association while preserving both marginals exactly.
      It must show NO gradient.  If it shows one, the stratification is
      manufacturing the effect and the arm is void.
  K2  planted boundary event: inject a coupling into the low-margin stratum only,
      of stated size, and confirm the stratified statistic recovers it.  This
      calibrates what gradient the arm can see.

No leakage, key-recovery or ECDLP claim.
"""
import argparse
import numpy as np
from ct_event_complete_v1 import (Lift, prime_order_curve, S9, g2_factorisation,
                                  spectrum_stats)

NBIN = 5


def stratified_counts(p, b=7, nbin=NBIN, verbose=True, shuffle_x=None):
    """Event-complete transitions, bucketed by the exact integer boundary margin.

    shuffle_x: if a Generator is passed, the x-coordinates are randomly permuted
    along d BEFORE lifting (control K3).  This preserves the MULTISET of lifts
    exactly -- hence every margin, every carry state, and the whole (state,margin)
    joint geometry -- while destroying the arithmetic order in d.  It separates
    'the gradient is deterministic lift geometry' from 'the gradient is arithmetic'.
    """
    pts, n = prime_order_curve(p, b)
    if pts is None:
        return None
    L = Lift(p)
    xs = np.array([pts[d][0] if d else 0 for d in range(n)], dtype=np.int64)
    if shuffle_x is not None:
        body = xs[1:].copy(); shuffle_x.shuffle(body); xs[1:] = body
    zx, zy = L.eis_array(xs)
    valid = np.ones(n, dtype=bool); valid[0] = False
    idx = np.arange(n, dtype=np.int64)
    DET = L.DET

    # ---- pass 1: exact margins, to fix the bin edges before any counting
    margins = []
    for g in range(1, n):
        e = (idx + g) % n
        sx = zx + zx[e]; sy = zy + zy[e]
        N1 = sx * L.R2[1] - sy * L.R2[0]
        N2 = -sx * L.R1[1] + sy * L.R1[0]
        c1 = Lift._rdiv_vec(N1, DET); c2 = Lift._rdiv_vec(N2, DET)
        M1 = DET - 2 * np.abs(N1 - c1 * DET)
        M2 = DET - 2 * np.abs(N2 - c2 * DET)
        m = np.minimum(M1, M2)
        ok = valid & valid[e]
        margins.append(m[ok])
    allm = np.concatenate(margins)
    edges = np.quantile(allm, np.linspace(0, 1, nbin + 1)[1:-1]).astype(np.int64)
    if verbose:
        print(f"  p={p} n={n}  DET={DET}  margin range [{allm.min()},{allm.max()}]")
        print(f"  exact-integer bin edges (quantiles): {list(edges)}")

    # ---- pass 2: accumulate 9x9 transition counts per stratum
    C = np.zeros((nbin, 9, 9), dtype=np.int64)
    Call = np.zeros((9, 9), dtype=np.int64)
    src_margin = []; src_state = []; dst_state = []
    for g in range(1, n):
        e = (idx + g) % n
        f = (idx + 2 * g) % n
        sx = zx + zx[e]; sy = zy + zy[e]
        N1 = sx * L.R2[1] - sy * L.R2[0]
        N2 = -sx * L.R1[1] + sy * L.R1[0]
        c1 = Lift._rdiv_vec(N1, DET); c2 = Lift._rdiv_vec(N2, DET)
        M1 = DET - 2 * np.abs(N1 - c1 * DET)
        M2 = DET - 2 * np.abs(N2 - c2 * DET)
        m = np.minimum(M1, M2)
        np.clip(c1, -1, 1, out=c1); np.clip(c2, -1, 1, out=c2)
        s = (3 * (c1 + 1) + (c2 + 1)).astype(np.int64)
        keep = valid & valid[e] & valid[f]      # d, d+g, d+2g all affine
        a = s[keep]; c = s[e][keep]; mm = m[keep]
        bins = np.searchsorted(edges, mm, side='right')
        Call += np.bincount(a * 9 + c, minlength=81).reshape(9, 9)
        for bnum in range(nbin):
            sel = bins == bnum
            if sel.any():
                C[bnum] += np.bincount(a[sel] * 9 + c[sel],
                                       minlength=81).reshape(9, 9)
        src_margin.append(mm); src_state.append(a); dst_state.append(c)
    return (C, Call, n, np.concatenate(src_margin), np.concatenate(src_state),
            np.concatenate(dst_state), edges)


def gradient_report(C, label):
    rows = []
    for bnum in range(C.shape[0]):
        g2, df = g2_factorisation(C[bnum])
        N = int(C[bnum].sum())
        rows.append((bnum, N, g2, df, g2 / df if df else float('nan')))
    print(f"\n  {label}")
    print(f"    {'bin':>4} {'N':>10} {'G2':>10} {'df':>4} {'G2/df':>8}")
    for bnum, N, g2, df, r in rows:
        print(f"    {bnum:>4} {N:>10} {g2:>10.2f} {df:>4} {r:>8.3f}")
    lo, hi = rows[0][4], rows[-1][4]
    print(f"    gradient  G2/df(lowest margin) - G2/df(highest) = {lo - hi:+.3f}")
    return rows, lo - hi


def control_K1(src_margin, src_state, dst_state, edges, nbin, rng):
    """Permute margin labels; states and transitions untouched."""
    perm = rng.permutation(len(src_margin))
    bins = np.searchsorted(edges, src_margin[perm], side='right')
    C = np.zeros((nbin, 9, 9), dtype=np.int64)
    for bnum in range(nbin):
        sel = bins == bnum
        if sel.any():
            C[bnum] += np.bincount(src_state[sel] * 9 + dst_state[sel],
                                   minlength=81).reshape(9, 9)
    return C


def control_K2(rng, nbin=NBIN, N=2_000_000, eps=0.02):
    """Plant a coupling in the low-margin stratum ONLY; must be recovered."""
    T1 = np.array([[.10, .80, .10], [.05, .90, .05], [.10, .80, .10]])
    T1 /= T1.sum(1, keepdims=True)
    C = np.zeros((nbin, 9, 9), dtype=np.int64)
    per = N // nbin
    for bnum in range(nbin):
        a = rng.choice(3, size=per, p=[.25, .5, .25])
        b = rng.choice(3, size=per, p=[.25, .5, .25])
        cum = np.cumsum(T1, axis=1)
        c = (rng.random(per)[:, None] > cum[a]).sum(1)
        if bnum == 0:                                  # boundary stratum
            T2p = T1.copy(); T2p[:, 0] += eps
            T2p = np.clip(T2p, 1e-12, None); T2p /= T2p.sum(1, keepdims=True)
            cum2 = np.cumsum(T2p, axis=1); cum1 = np.cumsum(T1, axis=1)
            u = rng.random(per)[:, None]
            d = np.where(c == 0, (u > cum2[b]).sum(1), (u > cum1[b]).sum(1))
        else:
            d = (rng.random(per)[:, None] > np.cumsum(T1, axis=1)[b]).sum(1)
        C[bnum] += np.bincount((3 * a + b) * 9 + (3 * c + d),
                               minlength=81).reshape(9, 9)
    return C


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", type=str, default="1009")
    ap.add_argument("--controls-only", action="store_true")
    ap.add_argument("--k3draws", type=int, default=20)
    args = ap.parse_args()
    rng = np.random.default_rng(20260724)

    print("=" * 78)
    print("CONTROL K2 — planted boundary-localised coupling must be RECOVERED")
    print("=" * 78)
    _, gK2 = gradient_report(control_K2(rng), "planted eps=0.02 in bin 0 only")
    print(f"  K2 FIRES (gradient clearly positive): {gK2 > 1.0}")

    if args.controls_only:
        raise SystemExit(0)

    for p in [int(t) for t in args.primes.split(",")]:
        print()
        print("=" * 78)
        print(f"REAL CURVE  p = {p}")
        print("=" * 78)
        r = stratified_counts(p)
        if r is None:
            print("  skipped (no prime-order curve)"); continue
        C, Call, n, sm, ss, ds, edges = r
        s = spectrum_stats(Call)
        print(f"  pooled over all strata: N={s['N']}  lambda2={s['l2']:.6f} "
              f"lambda3={s['l3']:.6f}  delta={s['delta']:.6f}")
        print(f"  pooled G2 = {s['g2']:.2f} / {s['df']} df   "
              f"(G2/df = {s['g2']/s['df']:.3f})")
        _, gr = gradient_report(C, "REAL, stratified by exact boundary margin")

        # K1 null DISTRIBUTION (20 draws), not a single draw
        gk = []
        for _ in range(20):
            Ck = control_K1(sm, ss, ds, edges, C.shape[0], rng)
            rows = [g2_factorisation(Ck[b]) for b in range(C.shape[0])]
            gk.append(rows[0][0] / rows[0][1] - rows[-1][0] / rows[-1][1])
        gk = np.array(gk)
        rank = 1 + int((gk <= gr).sum() if gr < 0 else (gk >= gr).sum())
        print(f"\n  CONTROL K1 (margin labels permuted, 20 draws)")
        print(f"    gradient null: mean {gk.mean():+.3f}  sd {gk.std(ddof=1):.3f}  "
              f"range [{gk.min():+.3f}, {gk.max():+.3f}]")
        print(f"    REAL gradient {gr:+.3f}   z = "
              f"{(gr - gk.mean())/gk.std(ddof=1):+.2f}   "
              f"rank-p = {rank}/21")

        # K3 ENSEMBLE: same lift multiset, arithmetic order in d destroyed.
        # A single draw has no error bar, so the "arithmetic remainder"
        # real - K3 cannot be read from one. Ensemble is mandatory.
        g3s = []; p3s = []
        for _ in range(args.k3draws):
            r3 = stratified_counts(p, shuffle_x=rng, verbose=False)
            rows = [g2_factorisation(r3[0][b]) for b in range(r3[0].shape[0])]
            g3s.append(rows[0][0] / rows[0][1] - rows[-1][0] / rows[-1][1])
            s3 = spectrum_stats(r3[1]); p3s.append(s3['g2'] / s3['df'])
        g3s = np.array(g3s); p3s = np.array(p3s)
        z3 = (gr - g3s.mean()) / g3s.std(ddof=1)
        print(f"\n  CONTROL K3 (x-coords permuted, {args.k3draws} draws) — "
              f"lift GEOMETRY kept, arithmetic order in d destroyed")
        print(f"    gradient:   {g3s.mean():+.3f} +- {g3s.std(ddof=1):.3f}   "
              f"range [{g3s.min():+.3f}, {g3s.max():+.3f}]")
        print(f"    pooled G2/df: {p3s.mean():.2f} +- {p3s.std(ddof=1):.2f}   "
              f"(REAL pooled {s['g2']/s['df']:.2f})")
        print(f"\n  SUMMARY p={p}")
        print(f"    REAL gradient          {gr:+.3f}")
        print(f"    K1 (stratification)    {gk.mean():+.3f} +- {gk.std(ddof=1):.3f}"
              f"   -> z_real = {(gr-gk.mean())/gk.std(ddof=1):+.2f}")
        print(f"    K3 (geometry only)     {g3s.mean():+.3f} +- "
              f"{g3s.std(ddof=1):.3f}   -> z_real = {z3:+.2f}"
              f"   ARITHMETIC REMAINDER = {gr - g3s.mean():+.3f}")
