#!/usr/bin/env python3
"""
Analytical test: does the cubic character χ₃(a) (order-3 φ(n)-residue rep on the
MULTIPLICATIVE unit group) connect to V(a) (the ADDITIVE character sum / sheaf)?

If the φ(n) law genuinely forces the eigenvalue structure, we'd expect SOME relationship
between χ₃(a) and V(a). If V(a) is identically distributed across the 3 cubic residue
classes of a, the multiplicative and additive structures are independent at the magnitude
level -- and the connection (if any) lives only at the CM/monodromy level, not the φ(n) level.

Stratify |u(a)|² (and the phase of V(a)) by χ₃(a)-class for a few small primes.
This is an analytical probe, not a pre-registered experiment -- exploratory.
"""
import sys
import numpy as np
from fractions import Fraction
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from twist_orbit_spectrum_run_v1 import signal

def cubic_class(a, n):
    """χ₃(a) = a^((n-1)/3) mod n, returns 0/1/2 for the three cubic residue classes.
    Requires n prime, n ≡ 1 mod 3."""
    if (n - 1) % 3 != 0:
        return None
    r = pow(a, (n - 1) // 3, n)
    # r is a cube root of 1 mod n; find which one by comparing to the three roots
    # the three cube roots of 1 mod n: find primitive cube root g^((n-1)/3) for generator g
    return r  # return the raw residue; we'll bucket by distinct values

def analyze(p):
    s = signal(p, 7)
    if s is None: return None
    n, c, X, Y = s
    if (n - 1) % 3 != 0:
        return {"p": p, "note": "n not ≡ 1 mod 3, no cubic character"}
    # compute V(a) for all a in (Z/n)* via FFT
    carr = np.asarray(c, dtype=np.complex128)
    V = np.fft.fft(carr)  # V[a] = sum_d c_d e^{2πi a d/n}
    # cubic classes of a: a^((n-1)/3) mod n
    classes = {}
    for a in range(1, n):
        r = pow(a, (n - 1) // 3, n)
        classes.setdefault(r, []).append(a)
    if len(classes) != 3:
        return {"p": p, "note": f"cubic character gives {len(classes)} classes (expected 3)"}
    # stratify |V(a)|² / (4p) = |u(a)|² by cubic class
    results = {}
    for r, alist in classes.items():
        u2_vals = [abs(V[a])**2 / (4*p) for a in alist]
        # also the phase of V(a) (angle)
        phases = [np.angle(V[a]) for a in alist]
        # mean of u², mean phase (circular), count
        mean_u2 = np.mean(u2_vals)
        # circular mean of phase
        C = np.mean(np.cos(phases)); S = np.mean(np.sin(phases))
        mean_phase = np.arctan2(S, C)
        results[r] = {"count": len(alist), "mean_u2": float(mean_u2),
                      "mean_phase": float(mean_phase),
                      "std_u2": float(np.std(u2_vals))}
    # the three classes should be (n-1)/3 each
    return {"p": p, "n": int(n), "classes": {str(k): v for k, v in results.items()}}

print("=== Analytical probe: stratify V(a) by cubic residue class χ₃(a) ===\n", flush=True)
print("Question: is the multiplicative cubic structure (φ(n) law) connected to the\n"
      "additive sheaf values V(a)? If mean|u|² is equal across the 3 classes, they're\n"
      "independent at the magnitude level.\n", flush=True)

for p in [127, 211, 547, 823, 1051]:
    res = analyze(p)
    if res is None:
        print(f"p={p}: signal failed", flush=True); continue
    if "note" in res:
        print(f"p={p}: {res['note']}", flush=True); continue
    print(f"p={p}  n={res['n']}  (n-1)/3 = {(res['n']-1)//3} classes:", flush=True)
    means = []
    for r, v in res["classes"].items():
        print(f"  χ₃-class {r:>10}: count={v['count']:4d}  mean|u|²={v['mean_u2']:.5f}  "
              f"std={v['std_u2']:.5f}  mean∠V={np.degrees(v['mean_phase']):+7.1f}°", flush=True)
        means.append(v["mean_u2"])
    spread = max(means) - min(means)
    overall = np.mean(means)
    print(f"  → spread across classes: {spread:.5f}  (relative to mean {overall:.5f}: {spread/overall*100:.1f}%)", flush=True)
    if spread / overall < 0.05:
        print(f"  → INDEPENDENT at magnitude level (cubic character doesn't affect |V|)", flush=True)
    else:
        print(f"  → POSSIBLE CONNECTION (magnitude differs across cubic classes) — investigate", flush=True)
    print(flush=True)

print("=== Analytical finding ===", flush=True)
print("If mean|u|² is ~equal across the 3 cubic classes at every prime, the multiplicative", flush=True)
print("φ(n) structure (cubic character) and the additive sheaf (V(a)) are INDEPENDENT at the", flush=True)
print("magnitude level. The 120° law (eigenvalue ratio = ζ₃) would then be a CM/monodromy", flush=True)
print("fact, NOT a φ(n)-residue-representation fact. The bridge's χ₃ and the eigenvalue's ζ₃", flush=True)
print("would be DIFFERENT μ₃'s that happen to coincide in value, not the same group element.", flush=True)
print("If they DIFFER across classes, there's a real φ(n)-level connection to chase.", flush=True)
