#!/usr/bin/env python3
"""
bilinear_diffset_v1.py — the two-point / difference-set object on the 82 keys.

Closure's OWN named complement (Lemma R bounds single sums; the stance principle
"only a joint property of the SET survives the ECDLP scramble" is exactly this).
Flagged four sessions, built in none. Built here with the guards this session earned:
  - matched null = random 82-key sets in the SAME dyadic bands (our-own-pipeline set),
  - rank verdict (never the tested set as its own baseline),
  - a POWER number (min detectable coherent fraction), and
  - the "what can this set produce?" check stated up front.

Object: for the 82 solved keys {d_i}, the difference set {[d_i-d_j]G : i>j} (3321 curve
points, computed exactly by scalar_mul(d_i-d_j)). We probe it with:
  (1) flap fraction  = frac of difference-points with eps != 0   (Cap Law: 1/4 if lifts
      equidistribute; a joint additive relation among the d_i would distort it),
  (2) S3 tensor      = |sum z^3|^2 of the difference-set lifts (the user's 3-D/3rd-order
      ask; exact Eisenstein), ranked vs matched null.

KNOWN-STRUCTURE CHECK (stated before running, per the session rule):
  d_i in [2^{P_i-1}, 2^{P_i}) with distinct P_i, so a difference d_i-d_j ~ 2^{max} is a
  well-mixed ~160-bit scalar => its lift is generic-looking for BOTH real and null. The
  y-SIGN of every positive difference is pinned (delta < n/2) => the antisymmetric y-part
  is DEGENERATE for these keys (reduces to the known smallness); we do NOT test it here and
  say so. The flap/S3 of the difference-set lift is the non-degenerate joint probe.

Exact signal path (int / Eisenstein-norm). Float only in the ranked display statistic.
"""
import os, csv, math, random
import numpy as np
from ecc_secp256k1 import scalar_mul, N_ORDER, P as SECP_P, _add
from int1_frame_operator_v1 import build_secp

HERE = os.path.dirname(os.path.abspath(__file__))


def emul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)


def ecube(z):
    return emul(emul(z, z), z)


def enorm(a, b):
    return a * a - a * b + b * b


def load_82():
    ds, bits, pts = [], [], []
    with open(os.path.join(HERE, "puzzles_verified.csv")) as f:
        for r in csv.DictReader(f):
            d = int(r["private_key"], 16)
            ds.append(d); bits.append(d.bit_length())
            pts.append((int(r["X"], 16), int(r["Y"], 16)))    # exact public point
    return ds, bits, pts


def diffset_stats(pts, eis, eps):
    """flap fraction + exact |sum z^3|^2 over {P_i - P_j : i>j}, via point subtraction."""
    J = [(x, y, 1) for (x, y) in pts]                 # Jacobian, Z=1
    flap = tot = 0; Sa = Sb = 0
    for i in range(len(J)):
        Xi, Yi, _ = J[i]
        for j in range(i):
            Xj, Yj, _ = J[j]
            D = _add((Xi, Yi, 1), (Xj, (-Yj) % SECP_P, 1))     # P_i + (-P_j)
            X, Y, Z = D
            if Z == 0:
                continue
            zi = pow(Z, SECP_P - 2, SECP_P)
            x = (X * zi * zi) % SECP_P
            z = eis(x); a, b = ecube(z); Sa += a; Sb += b
            tot += 1
            if eps(x) != 0:
                flap += 1
    return flap / tot, enorm(Sa, Sb), tot


def random_pts(bits, rng):
    return [scalar_mul(rng.randrange(1 << (b - 1), 1 << b)) for b in bits]


def main():
    print("BILINEAR DIFFERENCE-SET on the 82 solved keys  (the joint-SET / two-point object)")
    print("=" * 78)
    eis, eps = build_secp()
    ds, bits, pts = load_82()
    print(f"  82 keys, bit-lengths {min(bits)}..{max(bits)};  difference set = C(82,2) = "
          f"{82*81//2} curve points (exact point subtraction).")
    print("  KNOWN-STRUCTURE CHECK: differences are ~mixed 160-bit scalars => lifts generic")
    print("  for real AND null (non-degenerate); y-sign of positive diffs is pinned (skipped).\n")

    # real
    rff, rS3, npair = diffset_stats(pts, eis, eps)
    print(f"  REAL difference set: Npairs={npair}  flap_frac={rff:.4f}  (Cap-Law generic = 0.25)")

    # matched null
    B = 120
    rng = random.Random(20260716)
    print(f"  building matched null: {B} random-82-sets in the SAME dyadic bands ...")
    null_ff = []; null_S3 = []
    for _ in range(B):
        rp = random_pts(bits, rng)
        ff, S3, _ = diffset_stats(rp, eis, eps)
        null_ff.append(ff); null_S3.append(S3)
    null_ff = np.array(null_ff); null_S3 = np.array(null_S3, dtype=float)

    def rank(val, arr):
        return float((arr <= val).mean())

    # control: a held-out random set must sit mid-bulk
    ctrl = random_pts(bits, rng)
    cff, cS3, _ = diffset_stats(ctrl, eis, eps)

    print("\n  matched-null verdict (rank-pct in [0.025,0.975] = consistent with null):")
    print(f"    {'[ctrl] held-out random-82':30} flap_frac rank={rank(cff, null_ff):.3f}  "
          f"S3 rank={rank(cS3, null_S3):.3f}")
    fr = rank(rff, null_ff); sr = rank(rS3, null_S3)
    fflag = "ANOMALY" if (fr < 0.025 or fr > 0.975) else "null"
    sflag = "ANOMALY" if (sr < 0.025 or sr > 0.975) else "null"
    print(f"    {'REAL 82 keys':30} flap_frac rank={fr:.3f} => {fflag}   "
          f"S3 rank={sr:.3f} => {sflag}")
    print(f"    null flap_frac: mean={null_ff.mean():.4f} sd={null_ff.std():.4f} "
          f"(real {rff:.4f}, z={(rff-null_ff.mean())/(null_ff.std()+1e-12):+.2f})")

    # POWER: min coherent flap-bias detectable at 95% of null with 3321 pairs
    print("\n  POWER (flap_frac): the null sd sets the smallest detectable flap-fraction shift.")
    print(f"    null sd(flap_frac) = {null_ff.std():.5f}  => 2-sigma detectable shift "
          f"~ {2*null_ff.std():.4f} in flap fraction ({2*null_ff.std()*npair:.0f} of {npair} pairs).")
    print("    (unlike the N=82 single-point test, the difference set gives 3321 pairs of power.)")


if __name__ == "__main__":
    main()
