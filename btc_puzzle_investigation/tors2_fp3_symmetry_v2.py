#!/usr/bin/env python3
"""tors2_fp3_symmetry_v2.py -- exhaustive symmetry group of G over Fbar, via root permutations.

G (built + validated in v1) has degree 7 with ALL roots in F_{p^3}.  Any Mobius sigma with
G(sigma t) = nu * G(t) must PERMUTE the 7 roots, and a Mobius map is pinned by 3 points.
So enumerating the 7*6*5 = 210 triple-correspondences is EXHAUSTIVE over Fbar -- every candidate
symmetry, not a sample.  For each survivor we report the multiplier nu and whether sigma is
F_p-rational (the v1 result says none can be; this checks the geometric group regardless).
"""
import itertools
from tors2_fp3_symmetry_v1 import F3, build, polyval, roots_in_F3

def _pow(K,u,k):
    r=(1,0,0)
    for _ in range(k): r=K.mul(r,u)
    return r

def det(K, M):
    a, b, c, d = M; return K.sub(K.mul(a, d), K.mul(b, c))

def minv(K, M):
    a, b, c, d = M; dt = det(K, M)
    if dt == (0, 0, 0): return None
    i = K.inv(dt)
    return (K.mul(d, i), K.mul(K.sc(b, -1), i), K.mul(K.sc(c, -1), i), K.mul(a, i))

def mmul(K, M, N):
    a, b, c, d = M; e, f, g, h = N
    return (K.add(K.mul(a, e), K.mul(b, g)), K.add(K.mul(a, f), K.mul(b, h)),
            K.add(K.mul(c, e), K.mul(d, g)), K.add(K.mul(c, f), K.mul(d, h)))

def to_std(K, q):
    """matrix sending q0->0, q1->1, q2->inf"""
    q0, q1, q2 = q
    a = K.sub(q1, q2); b = K.mul(K.sc(q0, -1), a)
    c = K.sub(q1, q0); d = K.mul(K.sc(q2, -1), c)
    return (a, b, c, d)

def mobius(K, src, dst):
    Ms, Md = to_std(K, src), to_std(K, dst)
    Mdi = minv(K, Md)
    if Mdi is None or det(K, Ms) == (0, 0, 0): return None
    M = mmul(K, Mdi, Ms)
    return M if det(K, M) != (0, 0, 0) else None

def apply_m(K, M, t):
    a, b, c, d = M
    den = K.add(K.mul(c, t), d)
    if den == (0, 0, 0): return None                # infinity
    return K.mul(K.add(K.mul(a, t), b), K.inv(den))

if __name__ == "__main__":
    p, A, B = 43, 0, 7
    for e in (1, 2, 3):
        n, xR, yR, D, Fp, byd = build(p, A, B, e)
        K = F3(p, A, B)
        G = [0] * (len(D) + len(Fp) - 1)
        for i, c in enumerate(D):
            for j, c2 in enumerate(Fp): G[i + j] = (G[i + j] + c * c2) % p
        R = roots_in_F3(G, K)
        assert len(R) == 7
        Rset = set(R)
        found = []
        for tgt in itertools.permutations(R, 3):
            M = mobius(K, tuple(R[:3]), tgt)
            if M is None: continue
            img = []
            bad = False
            for r in R:
                u = apply_m(K, M, r)
                if u is None or u not in Rset: bad = True; break
                img.append(u)
            if bad or len(set(img)) != 7: continue
            # G(sigma t)*(ct+d)^7 == nu * G(t) ?  test at 12 sample points
            a_, b_, c_, d_ = M
            nu = None; ok = True
            for t in list(K.elems())[:400:37]:
                den = K.add(K.mul(c_, t), d_)
                if den == (0, 0, 0): continue
                lhs = K.mul(polyval(G, K.mul(K.add(K.mul(a_, t), b_), K.inv(den)), K),
                            _pow(K, den, 7))
                rhs = polyval(G, t, K)
                if rhs == (0, 0, 0):
                    if lhs != (0, 0, 0): ok = False; break
                    continue
                q = K.mul(lhs, K.inv(rhs))
                if nu is None: nu = q
                elif q != nu: ok = False; break
            if ok and nu is not None:
                rational = all(x[1] == 0 and x[2] == 0 for x in M)
                found.append((M, nu, rational))
        print("e=%d | Mobius maps permuting G's 7 roots: %d" % (e, len(found)))
        for M, nu, rat in found[:6]:
            print("     nu=%s  F_p-rational sigma: %s" % (nu, rat))
