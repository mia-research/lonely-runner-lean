#!/usr/bin/env python3
# Does the AGGREGATE mean|U| deficit (the -13.9 sigma of RESULT_harmonic_support_pattern) also
# fall under the +/- -preserving (Hermitian) null g(n-d)=conj(g(d))? Full 2D U(1,b,c).
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords

R = 200
def build_U(xi, yi, phase, p):
    H = np.zeros((p, p), dtype=complex); np.add.at(H, (xi, yi), phase)
    return np.fft.fft2(H)

def agg_mean(xi, yi, phase, p):
    U = np.abs(build_U(xi, yi, phase, p))
    BB, CC = np.meshgrid(np.arange(p), np.arange(p), indexing='ij')
    nz = ~((BB == 0) & (CC == 0))
    return U[nz].mean()

def herm_phase(n, rng):
    g = np.empty(n - 1, dtype=complex)
    for d in range(1, n):
        nd = n - d
        if d < nd:
            z = np.exp(2j * np.pi * rng.random()); g[d - 1] = z; g[nd - 1] = np.conj(z)
        elif d == nd:
            g[d - 1] = 1.0
    return g

def run(p, n, G, rng):
    xs, ys = group_coords(G, p, n, 0)
    xi = np.array(xs[1:], dtype=np.int64) % p; yi = np.array(ys[1:], dtype=np.int64) % p
    d = np.arange(1, n)
    mc = agg_mean(xi, yi, np.exp(2j * np.pi * d / n), p)
    P = [agg_mean(xi, yi, np.exp(2j * np.pi * rng.random(n - 1)), p) for _ in range(R)]
    Hn = [agg_mean(xi, yi, herm_phase(n, rng), p) for _ in range(R)]
    pm, ps = np.mean(P), np.std(P) + 1e-15
    hm, hs = np.mean(Hn), np.std(Hn) + 1e-15
    print(f"  p={p:5d}: char={mc:.4f}  plain={pm:.4f}({100*(mc-pm)/pm:+.3f}%, z={(mc-pm)/ps:+.1f})  "
          f"HERM={hm:.4f}({100*(mc-hm)/hm:+.3f}%, z={(mc-hm)/hs:+.1f})", flush=True)

def main():
    rng = np.random.default_rng(20260721)
    print("=== AGGREGATE mean|U| deficit: plain null vs +/- -preserving null ===", flush=True)
    for p0 in (163, 349, 433, 577, 991):
        run(*prime_order_curve(p0, p0 + 40), rng)
    print("READ: if z-vs-HERM ~0 => the aggregate -13.9sigma was also the wrong-null artifact.", flush=True)

if __name__ == "__main__":
    main()
