#!/usr/bin/env python3
"""
ct_event_complete_v1.py — ARM A of PREREG_xdomain_ports_v1.

The event-complete (all-step-sizes) transition operator C_T on the Eisenstein
addition-carry state, replacing the single-orbit estimate used by
ANOMALY_DRILL_01_CT_SPLIT_v1.

PRIOR INSTRUMENT (drill 01).  One generator G; state sequence
    s_k = state(eis(x_[k]G), eis(x_[k+1]G)),   k = 1..n-1
and C_T counts s_k -> s_{k+1}.  n transitions; floor ~ sqrt(30/n) ~ 1.7% at
n ~ 1e5; bound explicitly scoped "this orbit, this generator, this prime".

THIS INSTRUMENT.  s(P,Q) = state(eis(x_P), eis(x_Q)) is defined for ALL pairs.
For each step size g, the step-g chain is
    s_g[d] = s([d]G, [d+g]G),   transition  s_g[d] -> s_g[d+g].
Enumerating ALL n step sizes g and ALL n positions d gives n^2 transitions:
the COMPLETE population of the operator with the generator scope removed.
Cost is index arithmetic on one precomputed lift array, not n^2 point additions.

EXACTNESS.  Every quantity in the signal path is int64 and every division is the
exact integer rounded-division rdiv (q + 1 if 2r >= de else q).  For p <= 1e6 the
largest intermediate is ~ p^1.5 ~ 1e9 << 2^63, so int64 numpy IS exact integer
arithmetic here -- verified against the reference Python-int path by --selftest.
Float appears only in eigenvalues / G^2 computed FROM exact integer counts.
"""
import argparse
import numpy as np
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

S9 = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]
I9 = {s: i for i, s in enumerate(S9)}
BAD = 9                      # sentinel: state undefined (point at infinity)


# ------------------------------------------------------------------ curve
def add_c(A, B, p):
    if A is None: return B
    if B is None: return A
    x1, y1 = A; x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % p == 0: return None
        lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def prime_order_curve(p, b=7):
    """Return (G, n) for y^2=x^3+b over F_p if the group is cyclic of prime order."""
    G = None
    for x in range(1, p):
        r = (x * x * x + b) % p
        if r and pow(r, (p - 1) // 2, p) == 1:
            y = sqrt_mod(r, p)
            if y:
                G = (x, int(y)); break
    if G is None: return None, None
    pts = [None, G]; cur = G
    while True:
        cur = add_c(cur, G, p)
        if cur is None: break
        pts.append(cur)
        if len(pts) > 4 * p: return None, None
    # pts = [O, G, 2G, ..., (n-1)G]  =>  pts[d] = [d]G  and  n = len(pts).
    # (n = len(pts) - 1 would be the AFFINE-point count, not the group order;
    #  every index below is taken mod the GROUP ORDER, so that is the one needed.)
    n = len(pts)
    assert add_c(pts[n - 1], G, p) is None, "orbit did not close at n"
    if not all(n % q for q in range(2, int(n ** .5) + 1)): return None, None
    return pts, n


# ------------------------------------------------------- exact lift, vectorised
class Lift:
    """eis() and state() in exact int64 numpy. rdiv reproduced exactly."""

    def __init__(self, p):
        self.p = p
        R1, R2 = reduced_basis(p)
        self.R1, self.R2 = R1, R2
        self.DET = R1[0] * R2[1] - R1[1] * R2[0]
        assert self.DET != 0
        # normalise so DET > 0 (rdiv flips signs for negative denominators)
        if self.DET < 0:
            self.R1, self.R2 = R2, R1
            self.DET = -self.DET

    @staticmethod
    def _rdiv_vec(nu, de):
        """exact integer rounded division, de > 0, elementwise. int64 in/out."""
        q = nu // de                       # numpy int floor division == Python //
        r = nu - q * de                    # 0 <= r < de
        return q + (2 * r >= de)

    def eis_scalar(self, X):
        c1 = rdiv(X * self.R2[1], self.DET)
        c2 = rdiv(-X * self.R1[1], self.DET)
        return (X - (c1 * self.R1[0] + c2 * self.R2[0]),
                -(c1 * self.R1[1] + c2 * self.R2[1]))

    def eis_array(self, xs):
        X = np.asarray(xs, dtype=np.int64)
        c1 = self._rdiv_vec(X * self.R2[1], self.DET)
        c2 = self._rdiv_vec(-X * self.R1[1], self.DET)
        zx = X - (c1 * self.R1[0] + c2 * self.R2[0])
        zy = -(c1 * self.R1[1] + c2 * self.R2[1])
        return zx, zy

    def state_vec(self, z1x, z1y, z2x, z2y):
        """carry state of z1+z2, encoded 0..8 as 3*(c1+1)+(c2+1)."""
        sx = z1x + z2x; sy = z1y + z2y
        c1 = self._rdiv_vec(sx * self.R2[1] - sy * self.R2[0], self.DET)
        c2 = self._rdiv_vec(-sx * self.R1[1] + sy * self.R1[0], self.DET)
        np.clip(c1, -1, 1, out=c1); np.clip(c2, -1, 1, out=c2)
        return (3 * (c1 + 1) + (c2 + 1)).astype(np.int8)


# ------------------------------------------------- event-complete accumulation
def event_complete_counts(p, b=7, gmax=None, verbose=True):
    """Exact integer 9x9 transition counts over ALL step sizes and positions."""
    pts, n = prime_order_curve(p, b)
    if pts is None: return None
    L = Lift(p)
    xs = np.array([pts[d][0] if d else 0 for d in range(n)], dtype=np.int64)
    zx, zy = L.eis_array(xs)
    valid = np.ones(n, dtype=bool); valid[0] = False        # d = 0 is O

    idx = np.arange(n, dtype=np.int64)
    C = np.zeros((9, 9), dtype=np.int64)
    gs = range(1, n) if gmax is None else range(1, min(n, gmax + 1))
    for g in gs:
        e = (idx + g) % n                                    # d + g
        f = (idx + 2 * g) % n                                # d + 2g
        s = L.state_vec(zx, zy, zx[e], zy[e])                # s_g[d]
        ok = valid & valid[e]                                # both endpoints affine
        s_from = s
        s_to = s[e]                                          # s_g[d+g]
        m = ok & ok[e] & valid[f]
        a = s_from[m].astype(np.int64); c = s_to[m].astype(np.int64)
        C += np.bincount(a * 9 + c, minlength=81).reshape(9, 9)
    if verbose:
        print(f"  p={p} n={n}  transitions={C.sum()}  (single orbit would give {n})")
    return C, n


# --------------------------------------------------------------- statistics
def marginals(C):
    """Per-coordinate 3x3 counts implied by the 9x9 joint counts."""
    C1 = np.zeros((3, 3), dtype=np.int64)
    C2 = np.zeros((3, 3), dtype=np.int64)
    for i, (a, b) in enumerate(S9):
        for k, (c, d) in enumerate(S9):
            C1[a + 1, c + 1] += C[i, k]
            C2[b + 1, d + 1] += C[i, k]
    return C1, C2


def row_normalise(C):
    r = C.sum(1, keepdims=True).astype(float)
    r[r == 0] = 1.0
    return C / r


def tensor_of(T1, T2):
    Tf = np.zeros((9, 9))
    for si, (i, j) in enumerate(S9):
        for sk, (k, l) in enumerate(S9):
            Tf[si, sk] = T1[i + 1, k + 1] * T2[j + 1, l + 1]
    return Tf


def g2_factorisation(C):
    """Pooled G^2 for 'within each source state, the two next-coords are
    independent'. 9 tables x 4 df = 16 df (empty cells drop df, reported)."""
    G2 = 0.0; df = 0
    for i in range(9):
        tab = np.zeros((3, 3), dtype=np.int64)
        for k, (c, d) in enumerate(S9):
            tab[c + 1, d + 1] += C[i, k]
        N = tab.sum()
        if N == 0: continue
        rs = tab.sum(1); cs = tab.sum(0)
        exp = np.outer(rs, cs) / N
        nz = tab > 0
        G2 += 2 * np.sum(tab[nz] * np.log(tab[nz] / exp[nz]))
        df += (np.count_nonzero(rs) - 1) * (np.count_nonzero(cs) - 1)
    return G2, df


def spectrum_stats(C):
    T = row_normalise(C)
    C1, C2 = marginals(C)
    T1, T2 = row_normalise(C1), row_normalise(C2)
    Tf = tensor_of(T1, T2)
    ev = sorted((abs(z) for z in np.linalg.eigvals(T)), reverse=True)
    delta = abs(ev[1] - ev[2])
    D = T - Tf
    # swap channel S: (c1,c2) -> (c2,c1)
    perm = [I9[(b, a)] for (a, b) in S9]
    Ds = D[np.ix_(perm, perm)]
    D_even = (D + Ds) / 2; D_odd = (D - Ds) / 2
    g2, df = g2_factorisation(C)
    return dict(ev=ev, delta=delta, l2=ev[1], l3=ev[2],
                maxdev=float(np.max(np.abs(D))),
                fro=float(np.linalg.norm(D)),
                fro_even=float(np.linalg.norm(D_even)),
                fro_odd=float(np.linalg.norm(D_odd)),
                g2=g2, df=df, N=int(C.sum()))


# ------------------------------------------------------- controls (must fire)
def surrogate_counts(T1, T2, N, rng, eps=0.0):
    """Coupling-free surrogate: two INDEPENDENT 3-state chains with marginals
    T1, T2, sampled to the same total N.  eps > 0 plants a coupling of that
    size: the c2 transition row is tilted by eps depending on c1's next state."""
    C = np.zeros((9, 9), dtype=np.int64)
    # stationary starts
    def stat(T):
        w, v = np.linalg.eig(T.T)
        k = int(np.argmin(np.abs(w - 1))); s = np.real(v[:, k]); s = np.abs(s)
        return s / s.sum()
    p1, p2 = stat(T1), stat(T2)
    a = rng.choice(3, size=N, p=p1); b = rng.choice(3, size=N, p=p2)
    u1 = rng.random(N); u2 = rng.random(N)
    cum1 = np.cumsum(T1, axis=1); c = (u1[:, None] > cum1[a]).sum(1)
    T2e = T2.copy()
    if eps > 0:
        # tilt: when c1 lands on state 0, push c2 toward state 0 by eps
        T2p = T2.copy()
        T2p[:, 0] += eps; T2p = np.clip(T2p, 1e-12, None)
        T2p /= T2p.sum(1, keepdims=True)
        cum2a = np.cumsum(T2, axis=1); cum2b = np.cumsum(T2p, axis=1)
        d = np.where(c == 0,
                     (u2[:, None] > cum2b[b]).sum(1),
                     (u2[:, None] > cum2a[b]).sum(1))
    else:
        cum2 = np.cumsum(T2e, axis=1); d = (u2[:, None] > cum2[b]).sum(1)
    src = 3 * a + b; dst = 3 * c + d
    C += np.bincount(src * 9 + dst, minlength=81).reshape(9, 9)
    return C


# ----------------------------------------------------------------- selftest
def selftest():
    """Instrument validation ONLY -- no curve data is read here.
    (1) vectorised int64 lift/state == reference Python-int path, exactly.
    (2) the surrogate with eps=0 reproduces near-zero coupling statistics.
    (3) a planted coupling is RECOVERED (the control fires) at stated sizes."""
    print("=" * 74); print("SELFTEST 1 — exact int64 vector path == Python-int reference")
    ok = True
    for p in (1009, 10009, 100003):          # all p = 1 mod 3 (Eisenstein basis)
        L = Lift(p)
        rng = np.random.default_rng(0)
        xs = rng.integers(0, p, size=500)
        zx, zy = L.eis_array(xs)
        for i, X in enumerate(xs):
            rx, ry = L.eis_scalar(int(X))
            if (rx, ry) != (int(zx[i]), int(zy[i])): ok = False; break
        # state
        ys = rng.integers(0, p, size=500)
        wx, wy = L.eis_array(ys)
        sv = L.state_vec(zx, zy, wx, wy)
        for i in range(500):
            sx = int(zx[i]) + int(wx[i]); sy = int(zy[i]) + int(wy[i])
            c1 = rdiv(sx * L.R2[1] - sy * L.R2[0], L.DET)
            c2 = rdiv(-sx * L.R1[1] + sy * L.R1[0], L.DET)
            c1 = max(-1, min(1, c1)); c2 = max(-1, min(1, c2))
            if int(sv[i]) != 3 * (c1 + 1) + (c2 + 1): ok = False; break
        print(f"   p={p:>7}: vector path exact vs reference: {ok}")
        assert ok
    print("   => int64 numpy path is EXACT integer arithmetic (no float in signal path)")

    print("=" * 74); print("SELFTEST 2/3 — control calibration on synthetic chains")
    rng = np.random.default_rng(1)
    T1 = np.array([[.10, .80, .10], [.05, .90, .05], [.10, .80, .10]])
    T1 /= T1.sum(1, keepdims=True); T2 = T1.copy()
    for N in (10 ** 6, 10 ** 7):
        base = spectrum_stats(surrogate_counts(T1, T2, N, rng, 0.0))
        print(f"\n   N={N:>9}  eps=0.000 : delta={base['delta']:.5f} "
              f"G2={base['g2']:.2f}/{base['df']}df  maxdev={base['maxdev']:.5f}")
        for eps in (0.002, 0.005, 0.01, 0.02):
            s = spectrum_stats(surrogate_counts(T1, T2, N, rng, eps))
            print(f"   N={N:>9}  eps={eps:.3f} : delta={s['delta']:.5f} "
                  f"G2={s['g2']:.2f}/{s['df']}df  maxdev={s['maxdev']:.5f}")
    print("\n   => the plant must RAISE G^2 far above its df at the smallest eps")
    print("      that the arm claims power against; that is the firing criterion.")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--primes", type=str, default="")
    a = ap.parse_args()
    if a.selftest:
        selftest()
    elif a.primes:
        for p in [int(t) for t in a.primes.split(",")]:
            r = event_complete_counts(p)
            if r is None:
                print(f"  p={p}: skipped (no prime-order curve)"); continue
            C, n = r
            s = spectrum_stats(C)
            print(f"    lambda2={s['l2']:.6f} lambda3={s['l3']:.6f} "
                  f"delta={s['delta']:.6f}")
            print(f"    G2={s['g2']:.3f}/{s['df']}df  maxdev={s['maxdev']:.5f} "
                  f"||D||_F={s['fro']:.5f} (even {s['fro_even']:.5f}, "
                  f"odd {s['fro_odd']:.5f})")
    else:
        ap.print_help()
