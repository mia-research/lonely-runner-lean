#!/usr/bin/env python3
"""
n1_phase_cap_sweep_v1.py — is the N1 phase cap |sin t1 + sin t2| <= 1 ?

BACKGROUND (RESULT_xdomain_ports_v2.md section 1).  The four twisted Frobenius
eigenvalues of the chi2(y) sheaf all have modulus exactly sqrt(p) (p=13,43), and
the multiset is closed under alpha -> -conj(alpha) -- FORCED, because
chi2^{(k)}(-1) = (-1)^{(p^k-1)/2} alternates with k at p = 3 mod 4.  Hence the
four eigenvalues form two pairs {alpha, -conj(alpha)} and

    |V(a)| = 2 sqrt(p) * |sin t1 + sin t2|        (p = 3 mod 4)
    |V(a)| = 2 sqrt(p) * |cos t1 + cos t2|        (p = 1 mod 4, chi2(-1) = +1)

Four complex unit vectors, but only TWO real parameters.  The open question named
there is whether |sin t1 + sin t2| <= 1, i.e. whether

    S(p) := max_{a != 0} |V(a)| / sqrt(p)   <=   2 .

THE POINT OF THIS SCRIPT.  That bound involves only V_1, which lives on E(F_p) --
no extension field, no Newton identities.  Cost is O(p + n log n) per prime
instead of O(p^4), so it is answerable at hundreds of primes rather than two.

PRE-COMMITTED READINGS (frozen here, before the sweep is run):
  (R1) S(p) > 2 at ANY prime  =>  the 2 sqrt(p) cap is FALSE.  N1's framing
       ("half of the 4 sqrt(p) ceiling") would then be wrong, and the phase-pairing
       bound with it.  This is the falsifying outcome and it is a single integer
       away at every prime -- the arm cannot be talked out of it.
  (R2) S(p) <= 2 everywhere AND S(p) -> 2  =>  the "1/2" IS exactly the
       phase-pairing constraint; the true cap is 2 sqrt(p), attained asymptotically,
       and N1 is explained as a symmetry type rather than a bound.
  (R3) S(p) <= 2 everywhere but PLATEAUS below 2  =>  the cap is not tight and a
       FURTHER constraint on the phases exists; that constraint is then the object,
       and this run names it as the next question rather than claiming N1 closed.

FORCED, therefore carrying zero information (reported, never counted as evidence):
  * |V| is constant on mu6-orbits of a  (V(a) = V(a*lambda), DC1; and
    V(a) = chi2(-1) V(-a)), so the n-1 rows collapse to (n-1)/6 DISTINCT
    configurations.  Every denominator below is (n-1)/6, never n-1.
  * V(0) = sum_d chi2(y_d) is the untwisted sum and is excluded (a != 0).

COMPARISON READOUTS (context, not controls -- no inference is drawn from them):
  chi2(x)  : dim 2, ceiling 2 sqrt(p).  The record (M3 / RESULT_N1_reframed) finds
             chi2(x) and chi2(y) reach the SAME absolute magnitude ~2 sqrt(p);
             only their ceilings differ.  Printed to check that reframing holds
             out to much larger p than the 6 primes it was measured on.
  random   : a random unit-modulus target on the same group, same estimator.

Exact integers in the signal path (the Legendre symbol and the orbit); float only
in the FFT and the modulus taken from it.  No leakage, key-recovery or ECDLP claim.
"""
import argparse
import numpy as np
from sympy import nextprime, isprime
from row_budget_core_v1 import curve_orbit


def legendre_arr(v, p):
    """chi2 of each entry, exact: 0 / +1 / -1 via Euler's criterion."""
    e = pow(int((p - 1) // 2), 1, p - 1)
    out = np.zeros(len(v), dtype=np.int64)
    for i, x in enumerate(v):
        x = int(x) % p
        out[i] = 0 if x == 0 else (1 if pow(x, (p - 1) // 2, p) == 1 else -1)
    return out


def sweep_prime(p):
    r = curve_orbit(p)
    if r is None:
        return None
    X, Y, n = r
    # ---- HASSE GUARD (bug found in this script's first run, before any reading).
    # curve_orbit returns ord(G), NOT #E.  When the first point G happens to lie in
    # a small prime-order subgroup, ord(G) is prime and the primality filter accepts
    # it -- e.g. p=1951 returned n=5, p=11833 returned n=61, both impossible for #E
    # by Hasse.  Those rows are a different object entirely (a small subgroup, not
    # the curve group) and they dragged the means down.  Require |n-(p+1)| <= 2 sqrt p,
    # which forces n = #E and hence G a generator.
    if abs(n - (p + 1)) > 2 * np.sqrt(p):
        return None
    hy = legendre_arr(Y, p).astype(float); hy[0] = 0.0
    hx = legendre_arr(X, p).astype(float); hx[0] = 0.0
    sp = np.sqrt(p)
    Vy = np.abs(np.fft.fft(hy)); Vx = np.abs(np.fft.fft(hx))
    Sy = Vy[1:].max() / sp; Sx = Vx[1:].max() / sp
    rng = np.random.default_rng(p)
    g = np.exp(2j * np.pi * rng.random(n)); g[0] = 0
    Sr = np.abs(np.fft.fft(g))[1:].max() / sp
    # distinct configurations under mu6 (forced collapse)
    ncfg = (n - 1) // 6
    # is V purely imaginary (p=3 mod 4) or real (p=1 mod 4)?  forced check
    Vfull = np.fft.fft(hy)
    if p % 4 == 3:
        purity = np.max(np.abs(Vfull[1:].real)) / max(1e-30, np.max(np.abs(Vfull[1:])))
    else:
        purity = np.max(np.abs(Vfull[1:].imag)) / max(1e-30, np.max(np.abs(Vfull[1:])))
    return dict(p=p, n=n, Sy=float(Sy), Sx=float(Sx), Sr=float(Sr),
                ncfg=int(ncfg), pmod4=p % 4, purity=float(purity))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pmax", type=int, default=60000)
    ap.add_argument("--need3mod4", action="store_true")
    a = ap.parse_args()
    print("=" * 96)
    print("N1 PHASE CAP SWEEP — is S(p) = max_{a!=0}|V(a)|/sqrt(p) <= 2 ?")
    print("=" * 96)
    print(f"{'p':>7} {'n':>7} {'p%4':>4} {'cfgs':>7} {'S_y':>8} {'S_x':>8} {'S_rand':>8} "
          f"{'purity':>9}  {'>2?':>4}")
    rows = []
    p = 7
    viol = []
    while p < a.pmax:
        p = int(nextprime(p))
        if p % 3 != 1:
            continue
        if a.need3mod4 and p % 4 != 3:
            continue
        r = sweep_prime(p)
        if r is None:
            continue
        rows.append(r)
        bad = r["Sy"] > 2.0
        if bad: viol.append(r)
        if len(rows) <= 40 or bad or p > a.pmax * 0.9:
            print(f"{r['p']:>7} {r['n']:>7} {r['pmod4']:>4} {r['ncfg']:>7} "
                  f"{r['Sy']:>8.4f} {r['Sx']:>8.4f} {r['Sr']:>8.4f} {r['purity']:>9.1e}"
                  f"  {'YES' if bad else '.':>4}")
    S = np.array([r["Sy"] for r in rows])
    cfg = sum(r["ncfg"] for r in rows)
    print()
    print(f"  primes swept: {len(rows)}   total DISTINCT mu6 configurations: {cfg:,}")
    print(f"  max S_y over all primes = {S.max():.5f}   at p = {rows[int(S.argmax())]['p']}")
    print(f"  violations of S_y <= 2 : {len(viol)}")
    print(f"  purity (forced: V purely imaginary at p=3 mod 4, real at p=1 mod 4):"
          f" worst {max(r['purity'] for r in rows):.2e}")
    for lo, hi in ((0, 1000), (1000, 10000), (10000, 10 ** 9)):
        sel = [r for r in rows if lo <= r["p"] < hi]
        if sel:
            v = np.array([r["Sy"] for r in sel])
            print(f"   p in [{lo},{hi}): {len(sel):>4} primes  mean S_y {v.mean():.4f}  "
                  f"max {v.max():.4f}   mean S_x {np.mean([r['Sx'] for r in sel]):.4f}   "
                  f"mean S_rand {np.mean([r['Sr'] for r in sel]):.4f}")
    print()
    if viol:
        print("  (R1) FIRES: S(p) > 2 occurs => the 2 sqrt(p) cap is FALSE.")
    else:
        print("  (R1) does not fire. Whether (R2) or (R3) holds is read from the trend above.")


if __name__ == "__main__":
    main()
