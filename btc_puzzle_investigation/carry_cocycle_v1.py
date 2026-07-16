#!/usr/bin/env python3
"""
carry_cocycle_v1.py -- the 2-cocycle / carry frontier.

Cocycle rigidity (this session): the only 1-cocycle (chaining readout) on prime-order E is d = the
DLP. But H^2(Z/n,Z/n)=Z/n is NONTRIVIAL; its generator is the ADDITION CARRY
    c(P,Q) = [ d(P)+d(Q) >= n ]  in {0,1},
the extension data of Z/n^2 -> Z/n.  The carry is a COMPARISON (did d_P+d_Q wrap n) -- a classic DLP
lever if cheaply readable -- and it IS the (n,k,D) 'wraparound'.  Is it detectable from the CURVE
COORDINATES of P, Q, S=P+Q via a cheap readout?  Natural probe: the xy 2-cocycle DEFECT
    delta_xy(P,Q) = xy(S) - xy(P) - xy(Q) mod p,   xy(P)=X(P)*Y(P).

TEST: MI( carry ; cheap-coordinate-feature ), z vs shuffle.  FIRING CONTROL: feature = (msb d_P, msb
d_Q); carry is nearly determined by the two top bits (both>=n/2 -> carry=1; both<n/2 -> 0), so this
MUST give a large z -- proving the detector works.  If coordinate features give z~0 => carry not
leaked by coordinates (comparison stays hard); an outlier z => a real handle.

Full-size random d in [1,n) (the carry is only meaningful at full scale). Exact int signal path;
MI via integer tables; z vs integer-permutation null.
"""
import math, random
import numpy as np
from ecc_secp256k1 import P as FP, N_ORDER, scalar_mul


def mi_bin(feat, targ, m):
    """MI(feat mod m ; binary targ), bits."""
    fa = np.array([v % m for v in feat]); ta = np.array(targ)
    N = len(fa); j = np.zeros((m, 2))
    for a, c in zip(fa, ta):
        j[a, c] += 1
    j /= N; mx = j.sum(1); my = j.sum(0); s = 0.0
    for i in range(m):
        for c in range(2):
            if j[i, c] > 0:
                s += j[i, c]*math.log2(j[i, c]/(mx[i]*my[c]+1e-18)+1e-18)
    return s


def mi_z(feat, targ, m, nsh=40, seed=0):
    real = mi_bin(feat, targ, m)
    rng = np.random.default_rng(seed)
    ta = np.array(targ)
    sh = [mi_bin(feat, rng.permutation(ta), m) for _ in range(nsh)]
    return real, (real - np.mean(sh))/(np.std(sh)+1e-12)


def main():
    print("="*80)
    print("2-COCYCLE / CARRY probe: is c(P,Q)=[d_P+d_Q>=n] detectable from curve coordinates?")
    print("="*80)
    random.seed(1)
    NP = 2500
    dP = [random.randrange(1, N_ORDER) for _ in range(NP)]
    dQ = [random.randrange(1, N_ORDER) for _ in range(NP)]
    carry = [1 if dP[i] + dQ[i] >= N_ORDER else 0 for i in range(NP)]
    print("carry base rate = %.3f (expect ~0.5)" % (sum(carry)/NP))

    xy_def = []; x_def = []; xy_S = []; x_S = []; y_S_half = []; xy_ratio = []
    msb_ctrl = []; half = N_ORDER // 2
    for i in range(NP):
        s = (dP[i] + dQ[i]) % N_ORDER
        Xp, Yp = scalar_mul(dP[i]); Xq, Yq = scalar_mul(dQ[i]); Xs, Ys = scalar_mul(s)
        xyp = (Xp*Yp) % FP; xyq = (Xq*Yq) % FP; xys = (Xs*Ys) % FP
        xy_def.append((xys - xyp - xyq) % FP)          # the xy 2-cocycle defect
        x_def.append((Xs - Xp - Xq) % FP)              # group-law x residual
        xy_S.append(xys); x_S.append(Xs)
        y_S_half.append(1 if Ys < FP//2 else 0)
        xy_ratio.append((xys * pow((xyp*xyq) % FP, FP-2, FP)) % FP if (xyp*xyq) % FP else 0)
        msb_ctrl.append((1 if dP[i] >= half else 0)*2 + (1 if dQ[i] >= half else 0))

    print("\n MI( carry ; feature mod m ), z vs 40-shuffle:")
    tests = [
        ("xy_defect  (the 2-cocycle)", xy_def, 6),
        ("xy_defect  mod2", xy_def, 2),
        ("x_defect   (group-law res)", x_def, 6),
        ("xy(S)", xy_S, 6),
        ("x(S)", x_S, 6),
        ("y(S)-half", y_S_half, 2),
        ("xy_ratio   (mult defect)", xy_ratio, 6),
    ]
    for name, feat, m in tests:
        r, z = mi_z(feat, carry, m)
        flag = "  <== ABOVE FLOOR" if abs(z) > 4 else ""
        print("   %-28s mod%d : MI=%.4f  z=%+.1f%s" % (name, m, r, z, flag))
    # firing control
    r, z = mi_z(msb_ctrl, carry, 4)
    print("   %-28s      : MI=%.4f  z=%+.1f   <- CONTROL: must fire (carry ~ msb_P & msb_Q)" % ("msb(d_P),msb(d_Q) CTRL", r, z))
    print("\n READ: coordinate features z~0 + control fires => carry NOT leaked by coordinates")
    print("       (comparison stays DLP-hard). An above-floor coordinate feature => a real handle.")
    print("[done]")


if __name__ == '__main__':
    main()
