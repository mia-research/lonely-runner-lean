#!/usr/bin/env python3
"""
glv_sector_local_delta_v1.py

Two more knobs from the design map.

A) GLV-SECTOR SWEEP: construct d = (a + b*lambda) mod n with the Z[omega] mini-pair
   (a,b) placed in a chosen 6-sector of the (a,b) plane (the CM/"twist angle"), sweep
   the sector, and ask whether the POINT statistic co-moves. This is the CM-native
   version of the angle sweep. Plant fires.

B) LOCAL-delta PERTURBATION: "resonance in the integer when you change it." For base
   keys d0, walk delta=0..W and look at chi6(x([d0+delta]G)); test the walk for a
   spectral peak (DFT) vs a permutation null, and MI(bit of delta ; d(sextant)). A
   real periodicity => a local structure; flat => avalanche/ECDLP.

Exact ints in the signal path except ranked DFT/MI stats.
"""
import numpy as np
from ecc_secp256k1 import scalar_mul, N_ORDER
from eisenstein_lift_sextant_exact_v1 import lift_sextant, sextant
from angular_interference_scaling_v1 import chi6, conditional
import random
PY = random.Random(7)
LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72

# ---- A) GLV-sector sweep ----
def ab_in_sector(s, scale, tries=2000):
    """pick (a,b) ~ scale with exact 6-sextant == s (reuse the Eisenstein sextant on (a,b))."""
    for _ in range(tries):
        a = PY.randrange(1, scale); b = PY.randrange(1, scale)
        for sgn in ((a, b), (-a, b), (a, -b), (-a, -b)):
            if sextant(sgn[0], sgn[1]) == s:
                return sgn
    return (scale, 0)

def sweep_glv_sector():
    print("=== A) GLV-SECTOR SWEEP (construct d=a+b*lambda by (a,b) sector) ===")
    scale = 1 << 125
    feats = {"sextant": [], "chi6X": []}; V = []
    means = []
    for s in range(6):
        sx = []
        for _ in range(1200):
            a, b = ab_in_sector(s, scale)
            d = (a + b * LAM) % N_ORDER
            if d == 0: continue
            X, Y = scalar_mul(d)
            feats["sextant"].append(lift_sextant(X)); feats["chi6X"].append(chi6(X) or 0)
            V.append(s); sx.append(lift_sextant(X))
        means.append(sum(sx) / max(len(sx), 1))              # noqa: float (report)
    V = np.array(V)
    print("  per-sector mean point-sextant: " + "  ".join(f"{s}:{m:.2f}" for s, m in enumerate(means)))
    rng = np.random.default_rng(1)
    M = len(V); Ms = [3000, M] if M > 3000 else [M]
    for fn, fv in feats.items():
        fv = np.array(fv)
        z = conditional(fv, V, Ms, 200, rng)[-1][2]
        print(f"    MI({fn} ; GLV-sector): z={z:+.2f}  => {'SHADOW' if abs(z) > 4 else 'flat'}")
    # plant: point stat := input sector
    z = conditional(V.copy(), V, Ms, 200, rng)[-1][2]
    print(f"    [plant] sector-copy vs sector: z={z:.0f} (fires)")

# ---- B) local-delta perturbation ----
def sweep_local_delta():
    print("\n=== B) LOCAL-delta PERTURBATION (walk d0+delta, look for resonance) ===")
    W = 64; nbase = 120
    rng = np.random.default_rng(5)
    # per-base DFT peak of chi6 walk vs permutation null, aggregated
    obs_peaks = []; null_peaks = []
    all_delta_bit = []; all_dsext = []
    for _ in range(nbase):
        d0 = 1 + int.from_bytes(rng.bytes(32), "big") % (N_ORDER - 2)
        seq = []
        prev = None
        for dl in range(W):
            X, Y = scalar_mul((d0 + dl) % N_ORDER)
            seq.append(chi6(X) or 0)
            sx = lift_sextant(X)
            if dl > 0:
                all_delta_bit.append(dl & 1); all_dsext.append(sx)
        z6 = np.exp(2j * np.pi * np.array(seq) / 6)          # noqa: float (ranked DFT)
        spec = np.abs(np.fft.fft(z6 - z6.mean()))            # noqa: float
        obs_peaks.append(float(spec[1:W // 2].max()))        # noqa: float
        perm = z6[np.random.default_rng().permutation(W)]     # noqa: float
        specn = np.abs(np.fft.fft(perm - perm.mean()))        # noqa: float
        null_peaks.append(float(specn[1:W // 2].max()))       # noqa: float
    op = np.array(obs_peaks); npk = np.array(null_peaks)
    # rank: is the observed walk-peak distribution above the permuted one?
    from statistics import mean
    print(f"  mean walk DFT peak: obs={op.mean():.2f}  perm-null={npk.mean():.2f}  "  # noqa: float
          f"ratio={op.mean()/(npk.mean()+1e-9):.3f}  ({'RESONANCE' if op.mean() > npk.mean()*1.2 else 'flat'})")  # noqa: float
    # MI(delta parity ; sextant) -- does the local step parity leak into the point?
    rng2 = np.random.default_rng(2)
    db = np.array(all_delta_bit); ds = np.array(all_dsext)
    z = conditional(ds, db, [5000, len(db)], 200, rng2)[-1][2]
    print(f"  MI(sextant ; delta parity): z={z:+.2f}  => {'SHADOW' if abs(z) > 4 else 'flat'}")

if __name__ == "__main__":
    sweep_glv_sector()
    sweep_local_delta()
