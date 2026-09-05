#!/usr/bin/env python3
"""
glv_addition_markov_audit_v1.py

Audits the user's 9-state addition-rounding Markov finding (small-prime run):
  states (c1,c2) = Babai rounding of eis(x(kG)) + eis(x((k+1)G)) -> 36:6:1 law,
  transition matrix lambda2 ~ 0.34, gap ~0.66.

Three questions, exact where it matters (float only for eigenvalues of a
stochastic matrix -- a spectral readout, not a leakage decision):

 (1) STATE LAW = tensor square?  Confirm the 9-state distribution is
     (3/4:1/8:1/8) (X) (3/4:1/8:1/8) = 36:6:1, and that it is GROUP-LAW-INDEPENDENT
     (identical for independent random field elements, not curve points).

 (2) Is the TRANSITION MEMORY (lambda2~0.34) more than the shared-term overlap?
     Consecutive states share z_{k+1}, which ALONE induces a transition structure.
     CONTROL: rebuild the chain on the SAME lift multiset in RANDOM order (destroys
     the +G sequence, keeps the shared-term overlap). If real lambda2 == control
     lambda2, the memory is generic geometry; if real < control (more memory), the
     scalar step +G leaves a fingerprint -- a sequence effect worth escalating.

 (3) V_spread fully spread?  Confirm distinct-count ~ N, norm <= 3p (matches our
     'group law does not linearize' result).
"""
import math
import random
from collections import defaultdict, Counter
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod

from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm


def add_curve(P1, P2, p, b=7):
    if P1 is None: return P2
    if P2 is None: return P1
    x1, y1 = P1; x2, y2 = P2
    if x1 == x2:
        if y1 == y2:
            if y1 == 0: return None
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            return None
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def find_gen(p):
    for x in range(1, p):
        rhs = (x * x * x + 7) % p
        if pow(rhs, (p - 1) // 2, p) == 1:
            y = sqrt_mod(rhs, p)
            if y:
                return (x, int(y))
    return None


def trans_spectrum(states):
    """transition matrix over observed states; return (lambda2, gap, n_states)."""
    idx = {s: i for i, s in enumerate(sorted(set(states)))}
    m = len(idx)
    C = np.zeros((m, m))
    for a, b in zip(states[:-1], states[1:]):
        C[idx[a], idx[b]] += 1
    rows = C.sum(1, keepdims=True)
    T = np.divide(C, rows, out=np.zeros_like(C), where=rows > 0)
    ev = sorted((abs(e) for e in np.linalg.eigvals(T)), reverse=True)
    lam2 = ev[1] if len(ev) > 1 else 0.0
    return lam2, ev[0] - lam2, m


def main():
    p = 100003
    N = 20000
    R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def eis(X):
        c1 = rdiv(X * R2[1], DET); c2 = rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))

    def state_of(z1, z2):
        sx, sy = z1[0] + z2[0], z1[1] + z2[1]
        c1 = rdiv(sx * R2[1] - sy * R2[0], DET)
        c2 = rdiv(-sx * R1[1] + sy * R1[0], DET)
        zr = (sx - (c1 * R1[0] + c2 * R2[0]), sy - (c1 * R1[1] + c2 * R2[1]))
        return (c1, c2), zr

    G = find_gen(p)
    print(f"=== p={p}, N={N}, generator {G} ===\n")

    # consecutive-multiple lift sequence z_k = eis(x(kG))
    zs = []
    Pk = G
    for _ in range(N + 1):
        zs.append(eis(Pk[0]))
        Pk = add_curve(Pk, G, p)

    # ---- (1) STATE LAW ----
    st_curve = [state_of(zs[k], zs[k + 1])[0] for k in range(N)]
    cnt = Counter(st_curve)
    # independent random field elements (NOT curve points)
    rng = random.Random(7)
    st_rand = []
    for _ in range(N):
        z1 = eis(rng.randrange(p)); z2 = eis(rng.randrange(p))
        st_rand.append(state_of(z1, z2)[0])
    cntr = Counter(st_rand)
    pred = {(0, 0): 36 / 64, (0, 1): 6 / 64, (0, -1): 6 / 64, (1, 0): 6 / 64,
            (-1, 0): 6 / 64, (1, 1): 1 / 64, (1, -1): 1 / 64, (-1, 1): 1 / 64,
            (-1, -1): 1 / 64}
    print("(1) STATE LAW  (3/4:1/8:1/8)^{(x)2} = 36:6:1")
    print(f"    {'state':>8} {'curve':>8} {'rand-x':>8} {'predict':>8}")
    for s in sorted(pred):
        print(f"    {str(s):>8} {cnt[s]/N:>8.4f} {cntr[s]/N:>8.4f} {pred[s]:>8.4f}")
    print("    => curve == rand-x == prediction  means the state law is pure lift")
    print("       geometry (self-convolution), independent of the group law.\n")

    # ---- (2) TRANSITION MEMORY: real vs shared-term control ----
    lam2_r, gap_r, m_r = trans_spectrum(st_curve)
    # control: SAME lift multiset, RANDOM order (kills +G sequence, keeps overlap)
    order = list(range(N + 1)); random.Random(99).shuffle(order)
    zs_sh = [zs[i] for i in order]
    st_ctrl = [state_of(zs_sh[k], zs_sh[k + 1])[0] for k in range(N)]
    lam2_c, gap_c, m_c = trans_spectrum(st_ctrl)
    # stronger control: fresh independent lift each step (pure shared-term chain)
    zf = [eis(rng.randrange(p)) for _ in range(N + 1)]
    st_ind = [state_of(zf[k], zf[k + 1])[0] for k in range(N)]
    lam2_i, gap_i, m_i = trans_spectrum(st_ind)
    print("(2) TRANSITION MEMORY  lambda2 (2nd eigenvalue), gap = 1 - lambda2")
    print(f"    REAL   (consecutive kG):        lambda2={lam2_r:.4f}  gap={gap_r:.4f}")
    print(f"    CTRL-A (same lifts, shuffled):  lambda2={lam2_c:.4f}  gap={gap_c:.4f}")
    print(f"    CTRL-B (fresh indep lifts):     lambda2={lam2_i:.4f}  gap={gap_i:.4f}")
    print("    => REAL == CTRL means the memory is the shared-term overlap (generic);")
    print("       REAL lambda2 notably ABOVE the controls = a +G sequence fingerprint.\n")

    # ---- (3) V_spread:  V = eis(x(P_k + P_{k+1})) - folded(z_k + z_{k+1}) ----
    Pk = G; pts = [G]
    for _ in range(N + 1):
        Pk = add_curve(Pk, G, p); pts.append(Pk)
    Vnorm = []; Vset = set()
    for k in range(N):
        _, zr = state_of(zs[k], zs[k + 1])
        Psum = add_curve(pts[k], pts[k + 1], p)
        if Psum is None:
            continue
        z3 = eis(Psum[0])
        V = (z3[0] - zr[0], z3[1] - zr[1])
        Vset.add(V); Vnorm.append(enorm(V))
    Vnorm = np.array(Vnorm)
    print("(3) V_spread additive correction  (our result: fully spread, |V|^2 <= 3p)")
    print(f"    distinct V: {len(Vset)} / {len(Vnorm)}   max|V|^2/p = {Vnorm.max()/p:.3f}"
          f"   mean|V|^2/p = {Vnorm.mean()/p:.3f}")


if __name__ == "__main__":
    main()
