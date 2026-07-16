#!/usr/bin/env python3
"""
joint_set_xy_probe_v1.py -- the MULTI-KEY / joint-SET frontier (the Type-II / bilinear handle).

Motivation (KNOWN_FACTS v5.1):
  * the ONE stable surviving single-key signal is (X*Y) mod m vs D mod m -- xy shadows the
    construction residual D.  This session: xy is odd-in-d + mu3-covariant (the structural why).
  * the parity-obstruction model: d is invisible to LINEAR functionals of Q; extraction would need a
    BILINEAR / Type-II handle -- believed absent for a prime-field curve.  So: BUILD it and let it speak.

OBJECT (the named closure-theorem GAP, glv_closure_theorem_v2 sec7 -- the two-point addition panel):
  B(a,b) = sum_{d_P,d_Q} F(P_{d_P}, P_{d_Q}, P_{d_P+d_Q}) * e_n(a d_P + b d_Q),
  F = e_p(bP x_P + cP y_P + bQ x_Q + cQ y_Q + bS x_S + cS y_S),  S=P+Q  (x_S=x_{d_P+d_Q}).
This is genuinely bilinear when (bS,cS)!=0: it couples the two keys via the group law and does NOT
factor into single sums.  If max|B|/n is bounded (~polylog) => generic (the 2-var KS the gap needs,
no lever).  If it SCARS (grows like sqrt(n) or n) => a real bilinear handle.

CONTROLS (discipline -- the control MUST fire):
  * factoring baseline (bS=cS=0): B factors => max|B|/n ~ (max|T|/sqrt(n))^2 bounded.  Calibrates "no coupling".
  * PLANTED bilinear lever: g[dP,dQ] = e_n(K*dP*dQ mod n) -- a genuine bilinear form; max|B| MUST spike.

SIGNAL PATH EXACT: x_d,y_d,d are int; e_p/e_n are roots of unity (analytic-size, no key in path).
"""
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords


def Bmax(xs, ys, p, n, bP, cP, bQ, cQ, bS, cS):
    """max_{a,b} |B(a,b)| / n  for the addition-coupled two-point sum, via 2D-FFT."""
    xd = np.array([0]+[xs[d] for d in range(1, n)], dtype=np.int64)
    yd = np.array([0]+[ys[d] for d in range(1, n)], dtype=np.int64)
    # per-index phases
    fP = np.exp(2j*np.pi*((bP*xd + cP*yd) % p)/p); fP[0] = 0
    fQ = np.exp(2j*np.pi*((bQ*xd + cQ*yd) % p)/p); fQ[0] = 0
    # sum-point phase indexed by s = (dP+dQ) mod n
    fS = np.exp(2j*np.pi*((bS*xd + cS*yd) % p)/p); fS[0] = 0
    # g[dP,dQ] = fP[dP] fQ[dQ] fS[(dP+dQ)%n]
    idx = (np.add.outer(np.arange(n), np.arange(n))) % n
    g = np.outer(fP, fQ) * fS[idx]
    B = np.fft.fft2(g)          # B[a,b] = sum g e_n(-a dP - b dQ); magnitudes are what we want
    B[0, 0] = 0
    return float(np.max(np.abs(B)))/n


def Bmax_planted_rank1(n, eps=1.0):
    """planted RANK-1 ADDITIVE lever: g[dP,dQ] = e_n(dP+dQ) buried in generic noise at strength eps.
    B(a,b) concentrates at (a,b)=(1,1) -> max|B|/n spikes toward n (a real, detectable concentration).
    This is what max|B| CAN detect (rank-1/additive structure). NOTE: a MULTIPLICATIVE (pairing-like)
    bilinear e_n(dP dQ) gives a FLAT Gauss spectrum (max/n=1) that max|B| CANNOT see -- absence of that
    handle is instead the MOV fact (embedding degree ~254-bit, no efficient pairing on prime field)."""
    d = np.arange(n)
    lever = np.exp(2j*np.pi*(np.add.outer(d, d) % n)/n)          # rank-1: e_n(dP+dQ)
    rng = np.random.default_rng(n)
    noise = np.exp(2j*np.pi*rng.random((n, n)))                  # generic
    g = eps*lever + noise
    B = np.fft.fft2(g); B[0, 0] = 0
    return float(np.max(np.abs(B)))/n


def main():
    print("="*84)
    print("JOINT-SET / bilinear xy probe -- the two-point addition panel (named closure gap)")
    print("  max|B(a,b)|/n : bounded(~polylog)=generic/no lever ; grows(sqrt n / n)=a bilinear handle")
    print("="*84)
    for lo, hi in [(120, 240), (300, 460), (600, 760)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, n, G = r
        xs, ys = group_coords(G, p, n, 0)
        sn = math.sqrt(n)
        print("\n p=%d n=%d  (sqrt(n)=%.1f)" % (p, n, sn))
        # factoring baseline (no coupling): bS=cS=0
        base = Bmax(xs, ys, p, n, 1, 0, 1, 0, 0, 0)
        # coupled x-only (the closure-gap object): bS!=0
        coup_x = Bmax(xs, ys, p, n, 1, 0, 1, 0, 1, 0)
        # coupled with the xy-harmonic (odd+mu3): y on all three legs
        coup_xy = Bmax(xs, ys, p, n, 1, 1, 1, 1, 1, 1)
        # coupled, xy on the SUM leg only (S carries the shadow object)
        coup_S = Bmax(xs, ys, p, n, 1, 0, 1, 0, 1, 1)
        # planted controls (rank-1 additive) -- MUST spike toward n
        plant_full = Bmax_planted_rank1(n, eps=1.0)
        plant_weak = Bmax_planted_rank1(n, eps=0.3)
        print("   factoring baseline (bS=0)      max|B|/n = %6.2f  (/n = %.3f)" % (base, base/n))
        print("   coupled x-only  (bS=1)         max|B|/n = %6.2f  (/n = %.3f)" % (coup_x, coup_x/n))
        print("   coupled xy-harmonic (all legs) max|B|/n = %6.2f  (/n = %.3f)" % (coup_xy, coup_xy/n))
        print("   coupled xy on SUM leg          max|B|/n = %6.2f  (/n = %.3f)" % (coup_S, coup_S/n))
        print("   CTRL planted rank-1 (eps=1.0)  max|B|/n = %6.2f  (/n = %.3f)  <- MUST spike toward n" % (plant_full, plant_full/n))
        print("   CTRL planted rank-1 (eps=0.3)  max|B|/n = %6.2f  (/n = %.3f)  <- weak lever, still visible" % (plant_weak, plant_weak/n))

    print("\n READ: coupled/baseline max|B|/n ~ O(1) flat (generic O(n) 2-var Weil size); planted rank-1")
    print("       spikes to ~n (/n ~ 1). Coupled staying flat => NO additive/rank-1 bilinear handle, even")
    print("       with the xy-harmonic. (A MULTIPLICATIVE pairing-like handle gives a FLAT spectrum max|B|")
    print("       cannot see -- but that is absent by the ~254-bit MOV embedding degree [CITED].)")
    print("[done]")


if __name__ == '__main__':
    main()
