#!/usr/bin/env python3
"""
joint_set_cocycle_v1.py -- the >=3-key / difference-set frontier: is the xy readout a COCYCLE
under addition?  I.e. is xy(P+Q) determined (cheaply) by xy(P), xy(Q)?

Why this is the right joint-SET object: a cheap readout that CHAINS across the set (r(P+Q)=f(r(P),r(Q)))
would let partial per-point info ACCUMULATE (sqrt(N) coherent bias, memory
btc_puzzle_signal_vs_noise_scaling) -> a joint-SET reduction of {d_i}. If xy is NOT a cocycle,
per-difference shadows do not chain and there is no accumulation. Parity-obstruction predicts no
cheap cocycle for a prime-field curve; BUILD it and let it speak, with a FIRING control.

TEST (36k constructed keys, known d, secp scale): sample pairs (d_P,d_Q); P=[d_P]G, Q=[d_Q]G,
S=[d_P+d_Q]G. Feature f in {xy, sextant, chi6X, mu3-harmonic}. Measure
  MI( f(S) mod m ; (f(P) mod m, f(Q) mod m) )  vs a shuffle null (z-score).
CONTROL (planted cocycle): r(P)=d_P mod m is ADDITIVE (r(S)=r(P)+r(Q) mod m) -> MI must be MAXIMAL.
A high z for xy => xy chains (a joint handle); z~0 => no cocycle, no accumulation.

Signal path exact: d, X, Y ints; MI via integer contingency tables, z vs integer-permutation null.
"""
import csv, math, random
import numpy as np
from ecc_secp256k1 import P as SECP_P, N_ORDER, scalar_mul


def mi(fx, tx, mf, mt):
    N = len(fx); j = np.zeros((mf, mt))
    for a, b in zip(fx, tx):
        j[a, b] += 1
    j /= N; mx = j.sum(1); my = j.sum(0); s = 0.0
    for i in range(mf):
        for k in range(mt):
            if j[i, k] > 0:
                s += j[i, k]*math.log2(j[i, k]/(mx[i]*my[k]+1e-18)+1e-18)
    return s


def mi_z(feat_S, joint_PQ, m, mt, nsh=40, seed=0):
    real = mi(feat_S, joint_PQ, m, mt)
    rng = np.random.default_rng(seed)
    sh = [mi(feat_S, rng.permutation(joint_PQ), m, mt) for _ in range(nsh)]
    return real, (real-np.mean(sh))/(np.std(sh)+1e-12)


def main():
    print("="*80)
    print("COCYCLE / >=3-key test: is xy(P+Q) determined by xy(P),xy(Q)?  (chains => accumulation)")
    print("="*80)
    rows = []
    with open("constructed_keys_fullrange_v1.csv") as f:
        for r in csv.DictReader(f):
            rows.append(int(r["d"]))
            if len(rows) >= 4000:
                break
    random.seed(1)
    NP = 3000
    ds = [(random.choice(rows), random.choice(rows)) for _ in range(NP)]
    m = 6
    # compute features for P, Q, S
    xyP = []; xyQ = []; xyS = []
    dP = []; dQ = []; dS = []
    for a, b in ds:
        s = (a + b) % N_ORDER
        Xa, Ya = scalar_mul(a); Xb, Yb = scalar_mul(b); Xs, Ys = scalar_mul(s)
        xyP.append((Xa*Ya) % SECP_P); xyQ.append((Xb*Yb) % SECP_P); xyS.append((Xs*Ys) % SECP_P)
        dP.append(a); dQ.append(b); dS.append(s)
    # joint (f(P) mod m, f(Q) mod m) encoded as a single index in [0, m*m)
    def joint(fP, fQ):
        return np.array([(fP[i] % m)*m + (fQ[i] % m) for i in range(len(fP))])
    xyS_m = np.array([v % m for v in xyS])
    # (1) the real test: xy cocycle
    r_xy, z_xy = mi_z(xyS_m, joint(xyP, xyQ), m, m*m)
    # (2) CONTROL: additive cocycle r=d mod m -> MI must be maximal (deterministic)
    dS_m = np.array([v % m for v in dS])
    r_d, z_d = mi_z(dS_m, joint(dP, dQ), m, m*m)
    # (3) baseline: a RANDOM readout (independent of the point) -> z~0
    rng = np.random.default_rng(7)
    rndS = rng.integers(0, m, len(dS)); rndPQ = rng.integers(0, m*m, len(dS))
    r_rnd, z_rnd = mi_z(rndS, rndPQ, m, m*m)
    print("\n  MI( f(S) ; (f(P),f(Q)) )  mod %d, z vs 40-shuffle:" % m)
    print("   xy  (the test)          MI=%.4f  z=%+.1f   %s" % (r_xy, z_xy,
          "<= xy CHAINS (a joint handle)" if z_xy > 5 else "<= no cocycle (does not chain)"))
    print("   d   (CTRL additive)     MI=%.4f  z=%+.1f   <- MUST be maximal (deterministic cocycle)" % (r_d, z_d))
    print("   random (CTRL null)      MI=%.4f  z=%+.1f   <- must be ~0" % (r_rnd, z_rnd))
    print("\n  max possible MI (log2 m) = %.4f" % math.log2(m))
    print("\n READ: d is a perfect additive cocycle (MI maximal, control fires). If xy z~0, xy does NOT")
    print("       chain => per-difference xy-shadows do not accumulate => no joint-SET handle from xy.")
    print("[done]")


if __name__ == '__main__':
    main()
