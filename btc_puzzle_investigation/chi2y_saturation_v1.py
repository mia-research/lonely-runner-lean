#!/usr/bin/env python3
"""
Is chi2(y) anomalously FAR BELOW its cohomological ceiling? -- correctly normalized.

WHY THIS EXISTS: a previous pass dismissed the chi2(y) sub-bound with two bad arguments:
 (a) a parity test that compared max|V|/sqrt(p) across p mod 4 classes -- but the parity constrains
     the PHASE of V(a) (odd sequence => V purely imaginary), NOT the magnitude, and the classes were
     confounded by a strong n-trend with 3 vs 5 unmatched primes. A null there was guaranteed.
 (b) "chi2(x) (dim 2) and chi2(y) (dim 4) both measure ~2.0, so ~2 is a statistic artifact" -- a
     non-sequitur: it compares RAW values and erases the normalized object (x SATURATES its ceiling,
     y reaches HALF of its).

THE DECISIVE COMPARISON (same dimension, so the max-over-frequencies statistic is held fixed):
   additive f=bx+cy  -> pole order 3 -> dim H^1_c = 1+3 = 4 -> ceiling 4 sqrt(p)
   chi2(y)           -> #R = 4 (three 2-torsion zeros + odd-order pole at O) -> dim 4 -> ceiling 4 sqrt(p)
Same dim, same #frequencies, same estimator. If additive saturates ~0.85 while chi2(y) sits ~0.50,
the gap CANNOT be a statistic artifact and is a property of the chi2(y) sheaf.

Also reports chi2(x) (dim 2) and additive c=0 (dim 3) for context, and the exact PHASE test of the
parity (the observable the mechanism actually constrains).

Signal path exact int; float only in FFT magnitudes (analytic character-sum sizes), per folder rule.
"""
import math
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords, legendre

DIM = dict(add_cne=4, add_c0=3, chi2x=2, chi2y=4)


def add_max(xs, ys, p, n, want_c0, exhaustive=True, nsamp=4000, seed=0):
    """max_{a!=0} |U(a,b,c)| over (b,c): c==0 branch if want_c0 else c!=0."""
    xsA = np.array(xs, dtype=np.int64); ysA = np.array(ys, dtype=np.int64)
    best = 0.0
    if exhaustive:
        pairs = ([(b, 0) for b in range(1, p)] if want_c0
                 else [(b, c) for b in range(p) for c in range(1, p)])
    else:
        rng = np.random.default_rng(seed)
        pairs = ([(b, 0) for b in range(1, p)] if want_c0
                 else [(int(rng.integers(0, p)), int(rng.integers(1, p))) for _ in range(nsamp)])
    for b, c in pairs:
        ph = np.exp(2j * np.pi * ((b * xsA + c * ysA) % p) / p); ph[0] = 0.0
        U = np.abs(np.fft.fft(ph)); U[0] = 0.0
        m = float(U.max())
        if m > best: best = m
    return best


def chi2_max_and_phase(coord, p, n):
    """max_{a!=0}|V| and the exact phase character of V (purely real / purely imaginary)."""
    v = np.array([0] + [legendre(int(coord[d]), p) for d in range(1, n)], dtype=float)
    V = np.fft.fft(v); Vm = np.abs(V); Vm[0] = 0.0
    a = int(np.argmax(Vm))
    re, im = abs(V[a].real), abs(V[a].imag)
    kind = "imag" if im > 100 * re else ("real" if re > 100 * im else "mixed")
    # exact parity of the sequence: v_{n-d} = eps * v_d ?
    eps = 1 if pow(p - 1, (p - 1) // 2, p) == 1 else -1
    par_ok = all(v[d] == eps * v[(n - d) % n] for d in range(1, min(n, 500)))
    return float(Vm.max()), kind, ("odd" if eps == -1 else "even"), par_ok


def main():
    print("=" * 108)
    print("chi2(y) SATURATION vs its cohomological ceiling -- normalized (ceiling = dim * sqrt(p))")
    print("=" * 108)
    print("  DECISIVE: additive(c!=0) and chi2(y) BOTH have dim H^1_c = 4 (ceiling 4 sqrt p).")
    print("  If their saturations differ, the gap is NOT a max-over-frequencies artifact.\n")
    hdr = ("p", "n", "p%4", "add_cne/4sp", "add_c0/3sp", "chi2x/2sp", "chi2y/4sp", "V phase", "parity")
    print("  %-6s %-6s %-4s %-12s %-11s %-10s %-11s %-8s %s" % hdr)
    rows = []
    for lo, hi in [(60, 160), (200, 320), (400, 520), (700, 820), (1200, 1320), (2000, 2120)]:
        r = prime_order_curve(lo, hi)
        if not r: continue
        p, n, G = r
        xs, ys = group_coords(G, p, n, 0)
        sp = math.sqrt(p)
        ex = (p <= 520)
        a_cne = add_max(xs, ys, p, n, False, exhaustive=ex) / sp
        a_c0 = add_max(xs, ys, p, n, True, exhaustive=True) / sp
        cx, _, _, _ = chi2_max_and_phase(xs, p, n); cx /= sp
        cy, kind, par, ok = chi2_max_and_phase(ys, p, n); cy /= sp
        s = (a_cne / DIM['add_cne'], a_c0 / DIM['add_c0'], cx / DIM['chi2x'], cy / DIM['chi2y'])
        rows.append((p, n, s))
        print("  %-6d %-6d %-4d %-12.3f %-11.3f %-10.3f %-11.3f %-8s %s%s"
              % (p, n, p % 4, s[0], s[1], s[2], s[3], kind, par, "" if ok else " *PARITY MISMATCH*"))
    print("\n  SATURATION SUMMARY (fraction of the cohomological ceiling actually reached):")
    for i, k in enumerate(("add_cne (dim4)", "add_c0 (dim3)", "chi2x (dim2)", "chi2y (dim4)")):
        vals = [r[2][i] for r in rows]
        print("    %-16s mean=%.3f  range=[%.3f, %.3f]" % (k, sum(vals)/len(vals), min(vals), max(vals)))
    print("\n  Read: compare 'add_cne (dim4)' vs 'chi2y (dim4)' -- SAME dim, SAME ceiling, SAME estimator.")
    print("  A large systematic gap there is a property of the chi2(y) sheaf, not of the statistic.")


if __name__ == "__main__":
    main()
