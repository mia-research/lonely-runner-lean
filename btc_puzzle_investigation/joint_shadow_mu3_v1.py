#!/usr/bin/env python3
"""
joint_shadow_mu3_v1.py -- μ6-ISOTYPE decomposition of the aligned readouts, run as a
CONSERVATION HUNT (not a null-confirmation).

Aut(E)=μ6 acts on the scalar d by d↦λd (GLV, λ³≡1 mod n) and d↦−d (negation). On the
coordinates: x_{λd}=β x_d (β³≡1 mod p), y_{λd}=y_d, x_{−d}=x_d, y_{−d}=−y_d. Any function
of d splits into 6 μ6-isotypes (μ3-weight w∈{0,1,2}) × (parity s∈{+,−}). The DL character
c(d)=e_n(a₀d) is what separates d from its μ6-orbit {±d,±λd,±λ²d}.

METHOD (per the standing protocol): hunt EXACT conservations (inner products = 0), and for
each, name the symmetry that enforces it; then look at the COMPLEMENT (channels the symmetry
does NOT force to zero) for concentration/anomaly. Structure that distinguishes d must live
outside the μ6-invariant (trivial-isotype) part.

WHAT IS MEASURED
 1. Conservation identities (exact, integer/label): x_{λd}=βx_d, y_{λd}=y_d, x_{−d}=x_d,
    y_{−d}=−y_d.  [must be 0 error]
 2. Character equipartition: energy of c in each of the 6 isotypes.  (conservation if =1/6 each)
 3. Cross-isotype zeros: ⟨F_iso, c_iso'⟩ for iso≠iso'  (μ6 Schur ⇒ must be 0; hunt EXTRA zeros).
 4. The 0.665 x-only alignment, split by μ3-weight w: flat (each ~0.665/√3) or concentrated?
    Same for the joint readout across the full 6-cell grid.
 5. char-vs-RANDOM per channel: is any concentration specific to c, or generic to the geometry?

CONTROLS  planted full-correlation readout F=c → each channel = its share (calibration);
    random unit-phase target on every channel (matched null).
SCOPE  enumerable model primes p≤~450, y²=x³+7. No claim about secp magnitudes; object structure.
FLOAT CARVE-OUT: analytic-size character sums; curve arithmetic exact int (t_y_maxbound_v1).
"""
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords
from joint_shadow_decompose_v1 import build_U, sep_mask, joint_mask, EPS

OMEGA = np.exp(2j * np.pi / 3)


def order3(m):
    for lam in range(2, m):
        if pow(lam, 3, m) == 1:
            return lam
    return None


def ip(f, g):
    """<f,g> = mean_{d=1..n-1} f[d] conj(g[d]) (index 0 excluded)."""
    return np.mean(f[1:] * np.conj(g[1:]))


def mu3_w(f, Lidx, w):
    """weight-w μ3 projection: (1/3)(f[d] + ω^{-w} f[λd] + ω^{-2w} f[λ²d])."""
    fL = f[Lidx]
    fL2 = f[Lidx[Lidx]]
    return (f + OMEGA ** (-w) * fL + OMEGA ** (-2 * w) * fL2) / 3.0


def parity(f, Midx, s):
    """s=+1 even, s=-1 odd part in d."""
    return 0.5 * (f + s * f[Midx])


def aligned_Fd(U, xs, ys, p, n, mask):
    """Aligned readout F(P_d) as an array indexed by d (0..n-1, F[0]=0)."""
    m = mask & (np.abs(U) > EPS)
    Fh = np.zeros_like(U); Fh[m] = U[m] / np.abs(U[m]); Fh[0, 0] = 0.0
    Fg = np.fft.ifft2(Fh) * (p * p)
    xi = np.array(xs[1:], dtype=np.int64); yi = np.array(ys[1:], dtype=np.int64)
    F = np.zeros(n, dtype=complex); F[1:] = Fg[xi, yi]
    return F


def spectrum_Fd(xs, ys, p, n, g, mask):
    """Aligned readout for an arbitrary target g[d] (0..n-1): keep phases of g's (b,c)-spectrum."""
    xi = np.array(xs[1:], dtype=np.int64); yi = np.array(ys[1:], dtype=np.int64)
    H = np.zeros((p, p), dtype=complex); np.add.at(H, (xi, yi), g[1:])
    V = np.fft.fft2(H)
    m = mask & (np.abs(V) > EPS)
    Fh = np.zeros_like(V); Fh[m] = V[m] / np.abs(V[m]); Fh[0, 0] = 0.0
    Fg = np.fft.ifft2(Fh) * (p * p)
    F = np.zeros(n, dtype=complex); F[1:] = Fg[xi, yi]
    return F


def run(lo, hi):
    r = prime_order_curve(lo, hi)
    if not r:
        return
    p, n, G = r
    xs, ys = group_coords(G, p, n, 0)
    lam = order3(n); beta = order3(p)
    xarr = np.array(xs, dtype=np.int64); yarr = np.array(ys, dtype=np.int64)
    d = np.arange(n)
    Lidx = (lam * d) % n
    Midx = (n - d) % n
    print(f"\n=== p={p} n={n}  lam={lam}(ord3 mod n)  beta={beta}(ord3 mod p) ===")

    # (1) conservation identities (exact). β is the cube root PAIRED with this λ: derive from data.
    beta_data = int(xarr[Lidx[1]]) * pow(int(xarr[1]), p - 2, p) % p  # x_{λ·1}/x_1
    e1 = int(np.max(np.abs((beta_data * xarr - xarr[Lidx]) % p)))     # x_{λd} = β x_d
    e2 = int(np.max(np.abs((yarr[Lidx] - yarr) % p)))                 # y_{λd} = y_d
    e3 = int(np.max(np.abs((xarr[Midx] - xarr) % p)))                 # x_{-d} = x_d
    e4 = int(np.max(np.abs((yarr[Midx] + yarr) % p)))                 # y_{-d} = -y_d
    print(f"  [C] identities (β={beta_data} paired w/ λ)  x_λd=βx_d:{e1}  y_λd=y_d:{e2}  "
          f"x_-d=x_d:{e3}  y_-d=-y_d:{e4}  (all must be 0)")

    c = np.exp(2j * np.pi * 1 * d / n); c[0] = 0.0                     # character e_n(a0=1 * d)

    # (2) character equipartition across the 6 isotypes  (conservation if 1/6 each)
    print("  [C] character energy per isotype (w,parity):  (equipartition => 1/6=0.1667 each)")
    tot = float(np.mean(np.abs(c[1:]) ** 2))
    grid = {}
    for w in (0, 1, 2):
        cw = mu3_w(c, Lidx, w)
        for s in (+1, -1):
            cis = parity(cw, Midx, s)
            grid[(w, s)] = cis
            frac = float(np.mean(np.abs(cis[1:]) ** 2)) / tot
            print(f"        w={w} s={'+' if s>0 else '-'}: {frac:.4f}", end="")
        print()

    # (3)+(4) x-only aligned readout: alignment per μ3-weight (the 0.665), + cross-weight zeros
    U = build_U(xs, ys, p, n, a0=1)
    for label, mask in (("x-only(even)", sep_mask(p)), ("joint", joint_mask(p))):
        F = aligned_Fd(U, xs, ys, p, n, mask)
        l2 = math.sqrt(float(np.mean(np.abs(F[1:]) ** 2)))
        # diagonal (matching-weight) alignment and full 3x3 cross table
        diag = []
        offmax = 0.0
        for w in (0, 1, 2):
            Fw = mu3_w(F, Lidx, w)
            diag.append(abs(ip(Fw, c)) / l2)
            for wp in (0, 1, 2):
                if wp != w:
                    offmax = max(offmax, abs(ip(Fw, mu3_w(c, Lidx, wp))))
        rho2 = abs(ip(F, c)) / l2
        # channels add in phase (sum ≈ rho2) ⇒ flat reference is rho2/3, not rho2/√3
        print(f"  [{label:12s}] rho2={rho2:.4f}  per-μ3-weight |<F_w,c>|/||F||: "
              f"w0={diag[0]:.4f} w1={diag[1]:.4f} w2={diag[2]:.4f}   "
              f"(sum={sum(diag):.4f}, flat/3={rho2/3:.4f})  cross-weight max={offmax:.1e}")

    # (5) char vs RANDOM per μ3-weight, x-only support: is the weight-FLATNESS specific to c?
    #     statistic = weight imbalance std([w0,w1,w2]); ensemble of random targets = matched null.
    Fc = aligned_Fd(U, xs, ys, p, n, sep_mask(p))
    lc = math.sqrt(float(np.mean(np.abs(Fc[1:]) ** 2)))
    dc = np.array([abs(ip(mu3_w(Fc, Lidx, w), c)) / lc for w in (0, 1, 2)])
    imb_c = float(np.std(dc))
    rng = np.random.default_rng(p + 7)
    imb_r = []
    for _ in range(60):
        g = np.zeros(n, dtype=complex); g[1:] = np.exp(2j * np.pi * rng.random(n - 1))
        Fr = spectrum_Fd(xs, ys, p, n, g, sep_mask(p))
        lr = math.sqrt(float(np.mean(np.abs(Fr[1:]) ** 2)))
        dr = np.array([abs(ip(mu3_w(Fr, Lidx, w), g)) / lr for w in (0, 1, 2)])
        imb_r.append(float(np.std(dr)))
    imb_r = np.array(imb_r)
    below = int(np.sum(imb_r <= imb_c))
    print(f"  [char vs random, x-only weight-imbalance std]  char={imb_c:.4f}   "
          f"random={imb_r.mean():.4f}±{imb_r.std():.4f}   char<=random in {below}/60 draws  "
          f"(char weights: w0={dc[0]:.3f} w1={dc[1]:.3f} w2={dc[2]:.3f})")


def main():
    print("=" * 88)
    print("μ6-ISOTYPE decomposition of the aligned readouts -- conservation hunt")
    print("=" * 88)
    for lo, hi in [(150, 250), (250, 400), (400, 460)]:
        run(lo, hi)
    print("\n[done]")


if __name__ == "__main__":
    main()
