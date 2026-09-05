#!/usr/bin/env python3
"""
Second analytical pass: the first probe found that at SOME primes (547, 1051) the mean |u|²
is EXACTLY equal across the 3 cubic residue classes of a (bit-identical), while at others
(127, 211, 823) it differs substantially. That's not noise -- exact equality is a symmetry.

Test the hypothesis: the equality holds iff V(a) is an eigenfunction of multiplication by
a primitive cube root of unity mod n, i.e. V(λa) = ζ · V(a) for λ a fixed primitive cube
root of 1 mod n and ζ some phase. If so, the three cubic classes are related by a phase
rotation that preserves |V| -- a genuine multiplicative-structural symmetry of the additive
sheaf. That WOULD be a φ(n)-level connection.

Check: for each prime, does V(λa)/V(a) have constant phase across a (within a class)?
And does the equality-of-means correlate with n being prime vs composite, or p vs n mod 3?
"""
import sys
import numpy as np
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from twist_orbit_spectrum_run_v1 import signal

def primitive_cube_roots(n):
    """Find the three cube roots of 1 mod n (n prime, n≡1 mod 3)."""
    # find a generator, or just scan for an element of order 3
    for g in range(2, n):
        lam = pow(g, (n - 1) // 3, n)
        if lam != 1 and pow(lam, 3, n) == 1:
            return [1, lam, pow(lam, 2, n)]
    return None

def analyze(p):
    s = signal(p, 7)
    if s is None: return None
    n, c, X, Y = s
    if (n - 1) % 3 != 0: return {"p": p, "skip": "n not 1 mod 3"}
    roots = primitive_cube_roots(int(n))
    if roots is None: return {"p": p, "skip": "no cube roots"}
    lam = roots[1]  # primitive cube root
    n = int(n)
    carr = np.asarray(c, dtype=np.complex128)
    V = np.fft.fft(carr)
    # KEY TEST: is V(λa) = const_phase * V(a) for all a?
    # if V(λa)/V(a) has constant phase, V is an eigenfunction of the λ-multiplication operator
    ratios_phase = []
    ratios_mag = []
    for a in range(1, n):
        if abs(V[a]) < 1e-6: continue
        b = (lam * a) % n
        if abs(V[b]) < 1e-6: continue
        r = V[b] / V[a]
        ratios_phase.append(np.angle(r))
        ratios_mag.append(abs(r))
    phases = np.array(ratios_phase)
    mags = np.array(ratios_mag)
    # circular std of phase
    C = np.mean(np.cos(phases)); S = np.mean(np.sin(phases))
    R = np.sqrt(C*C + S*S)  # mean resultant length, 1=perfectly concentrated
    mean_phase = np.degrees(np.arctan2(S, C))
    return {"p": p, "n": n, "lambda": lam, "lam_cubed_mod_n": pow(lam,3,n),
            "n_phase_samples": len(phases),
            "phase_circular_mean_deg": float(mean_phase),
            "phase_concentration_R": float(R),  # 1.0 = constant phase
            "mag_mean": float(np.mean(mags)), "mag_std": float(np.std(mags))}

print("=== Analytical probe 2: is V(a) an eigenfunction of multiplication by λ (cube root of 1 mod n)? ===\n", flush=True)
print("If V(λa)/V(a) has CONSTANT phase (concentration R≈1.0), then V is an eigenfunction of\n"
      "the λ-multiplication operator -- a genuine φ(n)-level symmetry of the additive sheaf.\n"
      "This would be the concrete form of the φ(n) law connecting multiplicative and additive.\n", flush=True)

for p in [127, 211, 547, 823, 1051, 1303, 1831, 2503]:
    r = analyze(p)
    if r is None or "skip" in r:
        print(f"p={p}: {r}", flush=True); continue
    eigen = "EIGENFUNCTION" if r["phase_concentration_R"] > 0.95 else "not eigenfunction"
    print(f"p={p:5d} n={r['n']:5d}  λ={r['lambda']:5d} (λ³={r['lam_cubed_mod_n']} mod n)  "
          f"phase mean={r['phase_circular_mean_deg']:+7.1f}°  concentration R={r['phase_concentration_R']:.4f}  "
          f"|ratio| mean={r['mag_mean']:.3f}±{r['mag_std']:.3f}  → {eigen}", flush=True)

print(flush=True)
print("=== If R≈1.0 with phase ≈ 0° or 180°, V(λa) = ±V(a) -- the cubic residue classes are", flush=True)
print("    related by sign, |V| is invariant, and the multiplicative structure DOES connect", flush=True)
print("    to the additive sheaf. This would be the analytical form of the φ(n) law here. ===", flush=True)
