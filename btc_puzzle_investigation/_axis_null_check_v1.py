#!/usr/bin/env python3
# TRUST-BUT-VERIFY: is the b=0 axis deficit a WRONG-NULL artifact? (index line 210 caution)
# The character e_n(d) has g(n-d)=conj(g(d)) (Hermitian in d); the plain random null does NOT.
# Compare the axis deficit under (a) plain unit-phase null vs (b) a +/- -PRESERVING null
# g(n-d)=conj(g(d)). If the deficit VANISHES under (b), it was a null-mismatch artifact.
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords

R = 300
def axis_mean(phase, yv, p):
    H = np.zeros(p, dtype=complex); np.add.at(H, yv, phase)
    A = np.abs(np.fft.fft(H)); return A[1:].mean()          # mean over c!=0

def herm_phase(n, rng):
    g = np.empty(n - 1, dtype=complex)                       # index d=1..n-1 -> slot d-1
    for d in range(1, n):
        nd = n - d
        if d < nd:
            z = np.exp(2j * np.pi * rng.random()); g[d - 1] = z; g[nd - 1] = np.conj(z)
        elif d == nd:
            g[d - 1] = 1.0
    return g

def run(p, n, G, rng):
    xs, ys = group_coords(G, p, n, 0)
    yv = np.array(ys[1:], dtype=np.int64) % p
    d = np.arange(1, n)
    char = np.exp(2j * np.pi * d / n)                        # e_n(d): Hermitian g(n-d)=conj(g(d))
    mc = axis_mean(char, yv, p)
    # (a) plain null
    accP = 0.0
    for _ in range(R): accP += axis_mean(np.exp(2j * np.pi * rng.random(n - 1)), yv, p)
    plain = accP / R
    # (b) +/- -preserving null
    accH = 0.0
    for _ in range(R): accH += axis_mean(herm_phase(n, rng), yv, p)
    herm = accH / R
    print(f"  p={p:5d}(p%4={p%4}): |A|_char={mc:.4f}  plainnull={plain:.4f} ({100*(mc-plain)/plain:+.2f}%)  "
          f"HERMnull={herm:.4f} ({100*(mc-herm)/herm:+.2f}%)", flush=True)

def main():
    rng = np.random.default_rng(20260721)
    print("=== axis deficit vs plain null vs +/- -preserving (Hermitian) null ===", flush=True)
    for p0 in (163, 349, 433, 577, 991):
        run(*prime_order_curve(p0, p0 + 40), rng)
    print("READ: if deficit ~vanishes under HERMnull => WRONG-NULL artifact (line 210 caution confirmed).", flush=True)

if __name__ == "__main__":
    main()
