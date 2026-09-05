#!/usr/bin/env python3
"""
lift_band_spectral_v1.py -- PART 2 of the lift x band programme: full-group SPECTRAL profiling.

The sparse-sample MI test (lift_band_joint_v1.py) can only see a joint association if it survives
into a 21k point-cloud.  This file takes the complementary lens the user asked for: on a TOY prime-
order curve where the WHOLE group is enumerable, take d over a band [A,2A), and ask

  (1) where does the Fourier mass of the BAND residual derr(d) / k(d) sit?  (claim: fat low-freq,
      because derr is a sawtooth / continued-fraction object -- NOT one character)
  (2) what is the Fourier profile of the CURVE readouts  u(d),v(d),s(d),eps(d),sextant(d),sign(xy)(d)
      -- eis is a LATTICE reduction, outside the KS closure; is its spectrum FLAT (white in d) or
      does it carry non-white low-freq mass?
  (3) is there a SHARED above-floor low-frequency mode -- an interference pattern between two objects
      not obviously linked?  No overlap -> scoped, well-explained null.  Overlap -> power-scale it.

DISCIPLINE:
 * toy values are < 2^40 so the FFT (float) loses NO key bits -- float is exact-safe here and is used
   only as an analytic magnitude ranked against a SHUFFLE null (the white-in-d floor).
 * band residual + all curve readouts computed EXACT-int, then transformed.
 * per-mode power reported as a RATIO to the shuffle floor; a mode only counts if it beats the floor.
 * scan several curve sizes -- finite-size structure that decays is not a real low-freq mode.
 * grade; a flat spectrum is a scoped fact about that curve/band, not an analytical closure.
"""
import math
import numpy as np
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm, sextant
from t_y_maxbound_v1 import prime_order_curve, group_coords


def band_residual(off, A, M):
    """derr(off) = min_{1<=den<=M} |den*off - k*A|, k=nearest.  Exact int.  Also return best den (=n)."""
    best_e = None; best_den = 1
    two = 2 * A
    for den in range(1, M + 1):
        k = (2 * den * off + A) // two          # round(den*off/A), off>=0
        e = abs(den * off - k * A)
        if best_e is None or e < best_e:
            best_e = e; best_den = den
    return best_e, best_den


def power_spectrum(seq):
    """|FFT|^2 of a mean-removed sequence, normalized to sum 1.  seq real or complex."""
    x = np.asarray(seq, dtype=complex)
    x = x - x.mean()
    F = np.fft.fft(x)
    P = np.abs(F) ** 2
    s = P.sum()
    return P / s if s > 0 else P


def shuffle_floor(seq, reps=40, seed=0):
    """mean per-mode power of the SAME multiset in random d-order = the white-in-d floor."""
    rng = np.random.default_rng(seed)
    x = np.asarray(seq, dtype=complex)
    acc = np.zeros(len(x))
    for _ in range(reps):
        acc += power_spectrum(rng.permutation(x))
    return acc / reps


def low_freq_mass(P, kmax):
    """fraction of spectral power in modes 1..kmax (and its mirror)."""
    n = len(P)
    idx = list(range(1, kmax + 1)) + list(range(n - kmax, n))
    return float(P[idx].sum())


def profile(seq, label, kmax, reps=40, seed=0):
    P = power_spectrum(seq)
    F = shuffle_floor(seq, reps=reps, seed=seed)
    lf = low_freq_mass(P, kmax)
    lf_floor = low_freq_mass(F, kmax)
    # top above-floor mode
    n = len(P)
    ratio = P / (F + 1e-18)
    ratio[0] = 0
    top = int(np.argmax(ratio))
    topf = min(top, n - top)                     # fold to |frequency|
    return {
        'label': label, 'lf': lf, 'lf_floor': lf_floor, 'lf_excess': lf / (lf_floor + 1e-18),
        'top_mode': topf, 'top_ratio': float(ratio[top]),
        'P': P, 'ratio': ratio,
    }


def run_curve(lo, hi, bexp, M, kmax=16):
    r = prime_order_curve(lo, hi)
    if not r:
        print("  (no prime-order curve in [%d,%d])" % (lo, hi)); return None
    p, n, G = r
    A = 1 << (bexp - 1)
    if 2 * A > n:
        print("  band 2A=%d exceeds group n=%d; skip" % (2 * A, n)); return None
    xs, ys = group_coords(G, p, n, 0)            # xs[d], ys[d] for d=1..n-1
    eis, eps = build(p)

    ds = list(range(A, 2 * A))                    # the band
    L = len(ds)
    off = [d - A for d in ds]

    # ---- scalar-side BAND residual targets (exact) ----
    derr = np.empty(L, dtype=object); kden = np.empty(L, dtype=np.int64)
    for i, o in enumerate(off):
        e, den = band_residual(o, A, M)
        derr[i] = e; kden[i] = den
    derr_f = np.array([float(x) for x in derr])

    # ---- curve-side readouts (exact-int features) over the SAME d-band ----
    U = np.empty(L); V = np.empty(L); S = np.empty(L)
    EP = np.empty(L); SX = np.empty(L); SXY = np.empty(L)
    for i, d in enumerate(ds):
        x = xs[d]; y = ys[d]
        u, v = eis(x)
        U[i] = u; V[i] = v; S[i] = enorm((u, v))
        EP[i] = eps(x); SX[i] = sextant(u, v)
        SXY[i] = 1.0 if 2 * (x * y % p) < p else -1.0     # exact int comparison (no p/2 float)

    print("\n curve p=%d n=%d  band bexp=%d A=%d L=%d  Farey cap M=%d  kmax=%d" %
          (p, n, bexp, A, L, M, kmax))

    # ---- profiles ----
    tgt = {'derr': derr_f, 'k_den': kden.astype(float)}
    cur = {'eis_u': U, 'eis_v': V, 'norm_s': S, 'flap_eps': EP, 'sextant': SX, 'sign_xy': SXY}
    prT = {k: profile(v, k, kmax, seed=1) for k, v in tgt.items()}
    prC = {k: profile(v, k, kmax, seed=2) for k, v in cur.items()}

    print("  BAND targets (expect low-freq EXCESS >> 1 if fat-spectrum):")
    for k, P in prT.items():
        print("    %-8s low-freq mass=%.3f  floor=%.3f  excess=%5.1fx  top|f|=%d (%.1fx floor)" %
              (k, P['lf'], P['lf_floor'], P['lf_excess'], P['top_mode'], P['top_ratio']))
    print("  CURVE readouts (expect ~1x = white-in-d if pseudorandom; >1x low-freq = STRUCTURE):")
    for k, P in prC.items():
        print("    %-8s low-freq mass=%.3f  floor=%.3f  excess=%5.1fx  top|f|=%d (%.1fx floor)" %
              (k, P['lf'], P['lf_floor'], P['lf_excess'], P['top_mode'], P['top_ratio']))

    # ---- OVERLAP: does any curve readout share a BAND target's low-freq spectral shape? ----
    # Test both targets: derr (high-freq residual) AND k_den (the low-freq denominator = the structure).
    n_ = len(prT['derr']['P'])
    lfidx = list(range(1, kmax + 1)) + list(range(n_ - kmax, n_))
    rng = np.random.default_rng(3)
    for tname in ('derr', 'k_den'):
        print("  OVERLAP vs %s (Pearson of low-freq power spectra, curve-readout; +shuffle floor):" % tname)
        Pd = prT[tname]['P']
        dref = Pd[lfidx] - Pd[lfidx].mean()
        for k, P in prC.items():
            cvec = P['P'][lfidx] - P['P'][lfidx].mean()
            rho = float(np.dot(dref, cvec)) / (float(np.linalg.norm(dref) * np.linalg.norm(cvec)) + 1e-18)
            nulls = []
            for _ in range(200):
                cs = rng.permutation(cvec)
                nulls.append(float(np.dot(dref, cs)) /
                             (float(np.linalg.norm(dref) * np.linalg.norm(cs)) + 1e-18))
            z = (rho - np.mean(nulls)) / (np.std(nulls) + 1e-12)
            flag = "  <-- overlap above floor" if abs(z) > 3 else ""
            print("    %-5s x %-8s  rho=%+.3f  z=%+.1f%s" % (tname, k, rho, z, flag))
    return p, n


if __name__ == '__main__':
    print("=" * 92)
    print("PART 2 -- full-group SPECTRAL profile: band residual (fat?) vs curve lift readouts (white?)")
    print("=" * 92)
    # scan several curve sizes so finite-size wobble that decays is not mistaken for a real mode
    for lo, hi, bexp, M in [(2100, 4200, 11, 32),
                            (8200, 16400, 13, 48),
                            (33000, 66000, 15, 64)]:
        run_curve(lo, hi, bexp, M, kmax=16)
    print("\n[done]  Read: BAND excess>>1 confirms fat low-freq spectrum; CURVE excess~1 = white-in-d;")
    print("        OVERLAP z<3 on every readout = no shared mode (scoped null, with the reason).")
