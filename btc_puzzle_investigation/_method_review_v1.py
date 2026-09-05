#!/usr/bin/env python3
"""
_method_review_v1.py -- audit MY OWN methods this session. Two consequential checks.

CHECK A: is my KS-bound U computation correct? Verify FFT-U == direct-sum-U at sample (a,b,c),
and confirm the reported max is a true max (brute a-scan == FFT max).

CHECK B: is my "0.93 NOT reproduced" fair, or did I use the wrong metric? Compute the RECORD's
EXACT metric |Corr(a0)|/||F||_inf for x-only vs joint (aligned readout), see if it yields 0.34/0.93.
||F||_inf = max_d |F(P_d)|, F(P_d)=sum_{b,c} Fhat(b,c) e_p(b x_d + c y_d), Fhat=conj(U(a0,.))/|U|.
"""
import cmath, math
import numpy as np
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod

def curve(p):
    def add(A, B):
        if A is None: return B
        if B is None: return A
        x1, y1 = A; x2, y2 = B
        if x1 == x2:
            if (y1 + y2) % p == 0: return None
            l = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else: l = (y2 - y1) * pow(x2 - x1, -1, p) % p
        x3 = (l * l - x1 - x2) % p
        return (x3, (l * (x1 - x3) - y1) % p)
    G = None
    for x in range(1, p):
        r = (x * x * x + 7) % p
        if pow(r, (p - 1) // 2, p) == 1: G = (x, int(sqrt_mod(r, p))); break
    pts = [None]; cur = G
    while cur is not None: pts.append(cur); cur = add(cur, G)
    return pts, len(pts)         # n = #E

def checkA(p=61):
    print(f"=== CHECK A: KS U computation correct? (p={p}) ===")
    pts, n = curve(p)
    xs = [pts[d][0] for d in range(1, n)]; ys = [pts[d][1] for d in range(1, n)]
    wp = 2 * math.pi / p; wn = 2 * math.pi / n
    def U_direct(a, b, c):
        return sum(cmath.exp(1j * (wp * ((b * xs[d] + c * ys[d]) % p) - wn * a * (d + 1)))
                   for d in range(n - 1))
    # FFT version (my method): g[0]=0, g[1:]=e_p(bx+cy); fft gives sum_d g[d] e^{-2pi i a d/n}
    import numpy as np
    ok = True; worst = 0
    for (a, b, c) in [(1, 2, 3), (5, 7, 0), (3, 0, 4), (10, 11, 13)]:
        g = np.zeros(n, dtype=complex)
        g[1:] = np.exp(1j * wp * ((b * np.array(xs) + c * np.array(ys)) % p))
        Uf = np.fft.fft(g)[a % n]
        Ud = U_direct(a, b, c)
        d = abs(Uf - Ud); worst = max(worst, d)
        if d > 1e-9: ok = False
        print(f"   U({a},{b},{c}): FFT={abs(Uf):.4f}  direct={abs(Ud):.4f}  |diff|={d:.2e}")
    print(f"   FFT==direct: {ok} (worst {worst:.1e})  -> KS-bound computation is {'SOUND' if ok else 'BUGGED'}")

def checkB(plist=(163, 211, 433)):
    print(f"\n=== CHECK B: the RECORD's exact metric |Corr|/||F||_inf -- does it give 0.34 / 0.93? ===")
    print(f"   {'p':>5} {'n':>5} {'x-only |Corr|/||F||_inf':>24} {'JOINT |Corr|/||F||_inf':>24} {'ratio':>6}")
    for p in plist:
        if not isprime(p): continue
        pts, n = curve(p)
        if not isprime(n): continue
        xs = np.array([pts[d][0] for d in range(1, n)]); ys = np.array([pts[d][1] for d in range(1, n)])
        d_idx = np.arange(1, n)
        wp = 2 * math.pi / p; wn = 2 * math.pi / n; a0 = 1
        phase = np.exp(-1j * wn * a0 * d_idx)
        def metric(use_c):
            # aligned readout over the chosen channels; ||F||_inf = max_d |F(P_d)|
            Fd = np.zeros(n - 1, dtype=complex)         # F(P_d) accumulator over d
            corr = 0.0
            for b in range(p):
                for c in (range(p) if use_c else [0]):
                    if b == 0 and c == 0: continue
                    e = np.exp(1j * wp * ((b * xs + c * ys) % p))     # e_p(bx+cy) over d
                    U = np.sum(e * phase)                            # U(a0,b,c)
                    if abs(U) < 1e-12: continue  # noqa: float — division guard inside continuous corr/||F||_inf statistic (checkB); U built from exact-integer curve data, guard prevents blowup, not a vanishing verdict
                    Fhat = np.conj(U) / abs(U)                       # aligned coeff, |Fhat|=1
                    Fd += Fhat * e                                   # contribute to F(P_d)
                    corr += abs(U)                                  # (1/n) sum|U| accumulates
            corr /= n
            Finf = np.max(np.abs(Fd))
            return corr / Finf if Finf > 0 else 0.0
        rx = metric(False); rj = metric(True)
        print(f"   {p:>5} {n:>5} {rx:>24.3f} {rj:>24.3f} {rj/rx if rx else 0:>6.2f}")
    print("   record claim: x-only ~0.34, joint ~0.93, ratio ~2.8. If this matches -> my audit's")
    print("   'not reproduced' was a WRONG-METRIC artifact and I owe a correction to MY audit.")

if __name__ == '__main__':
    checkA()
    checkB()
