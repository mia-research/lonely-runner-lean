#!/usr/bin/env python3
"""
AUDIT: does the KS bound max_k|A_hat(k)|=O(p^{1/2}) hold for the eps-flap readout,
which is NOT e_p(rational f) but a Babai-lattice step function?

Theorem B/B1/B2 (bilinear_closure_proof_v1) require A=e_p(f), f rational bounded
degree; the doc verifies |A_hat|~2.5 sqrt(p) for the harmonic e_p(bx+cy). The
two-key null used A=eps(x). Here we compute max_{k!=0}|A_hat(k)| for BOTH over
the full group and fit the exponent alpha in max|A_hat| ~ C p^alpha.
alpha~0.5 => eps empirically obeys the KS-type bound (thesis holds, proof-gap only)
alpha>0.5 => the closure genuinely fails for the eps features.

Fourier over the CYCLIC group: A_hat(k)=sum_{u=0}^{n-1} A(x([u]G)) e_n(-ku).
Exact int signal path for features; the DFT magnitude is a monotone quantity we
only fit an exponent to (no threshold decides a verdict on float).
"""
import sys, math, cmath
sys.path.insert(0, ".")
import blinded_joint_readout_v1 as B
import int1_frame_operator_v1 as frm

def group_x_list(p):
    """x([u]G) for u=1..n-1 (u=0 is O, skip); returns (n, xs, ys)."""
    n, G = B.model_setup(p)
    xs = [None] * n; ys = [None] * n
    for u in range(1, n):
        Pu = B.mmul(u, G, p)
        if Pu is None:   # point at infinity (should not occur for u<n)
            continue
        xs[u], ys[u] = Pu
    return n, G, xs, ys

def maxhat(vals, n):
    """max_{k!=0} |sum_u vals[u] e_n(-k u)|, vals indexed by u in 0..n-1 (u=0 -> 0)."""
    m = 0.0
    twopi = 2 * math.pi
    for k in range(1, n):
        s = 0j
        wk = twopi * k / n
        for u in range(1, n):
            v = vals[u]
            if v:
                s += v * cmath.exp(-1j * wk * u)
        a = abs(s)
        if a > m: m = a
    return m

def main():
    primes = [547, 907, 1303, 1669, 2089]  # prime curve order (blinded model curves); G generates
    print(f"{'p':>6} {'n':>6} | {'eps_max/√p':>11} {'harm_max/√p':>12} | eps_max harm_max")
    data = []
    for p in primes:
        n, G, xs, ys = group_x_list(p)
        eis, eps = frm.build(p)
        # eps-flap centered
        epsv = [0.0] * n
        for u in range(1, n): epsv[u] = float(eps(xs[u]))
        mean_eps = sum(epsv[1:]) / (n - 1)
        epsc = [0.0] + [epsv[u] - mean_eps for u in range(1, n)]
        # harmonic e_p(b x + c y), b=1,c=1 (pole order <=3), centered automatically (oscillatory)
        harm = [0.0] * n
        harm = [None] * n
        harm[0] = 0j
        for u in range(1, n):
            harm[u] = cmath.exp(2j * math.pi * ((xs[u] + ys[u]) % p) / p)
        e_max = maxhat(epsc, n)
        h_max = maxhat(harm, n)
        rp = math.sqrt(p)
        print(f"{p:>6} {n:>6} | {e_max/rp:>11.3f} {h_max/rp:>12.3f} | {e_max:8.1f} {h_max:8.1f}")
        data.append((p, e_max, h_max))
    # fit exponent alpha: log(max) = alpha log(p) + c
    def fit(xs_p, ys_v):
        lx = [math.log(p) for p in xs_p]; ly = [math.log(v) for v in ys_v]
        nX = len(lx); mx = sum(lx)/nX; my = sum(ly)/nX
        num = sum((lx[i]-mx)*(ly[i]-my) for i in range(nX))
        den = sum((lx[i]-mx)**2 for i in range(nX))
        return num/den
    ps = [d[0] for d in data]
    print(f"\nfitted exponent alpha (max|A_hat| ~ p^alpha):")
    print(f"  eps-flap : alpha = {fit(ps,[d[1] for d in data]):.3f}   (KS bound => 0.5)")
    print(f"  harmonic : alpha = {fit(ps,[d[2] for d in data]):.3f}   (doc: ~0.5, |A_hat|~2.5√p)")

if __name__ == "__main__":
    main()
