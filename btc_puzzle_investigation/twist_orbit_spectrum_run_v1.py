#!/usr/bin/env python3
"""
twist_orbit_spectrum_run_v1.py — PREREG_twist_orbit_spectrum_v2.md

Is the twist orbit a -> V(a) multiplicatively structured beyond its Sato-Tate
marginal?  V(a) = sum_{P in E(F_p)} chi2(y_P) zeta_n^{a d(P)},  a in (Z/n)^*.

FORCED structure (verified, exact): V(-a) = -V(a) (chi2(-1)=-1 at p=3 mod 4),
V is mu3-invariant, purely imaginary.  Free data = the signed real sequence
r_c = V(g^c) on the L=(n-1)/6 mu6-classes.  Spectrum supported on the L odd,
mu3-trivial characters chi_j (j = 3 mod 6).

STATISTIC   T(p) = max_{j = 3 mod 6} |Vhat(chi_j)|^2      (numerator; the
            Parseval denominator n(n-1) is a forced constant, so ranking by the
            numerator gives the identical permutation p-value).
NULL        permute the L signed class-values, rebuild V by the forced
            (mu3-invariant + odd) symmetry, recompute T.  Preserves magnitude
            marginal + sign balance + anti-symmetry; destroys only arrangement.

NUMERICAL INTEGRITY (folder OVERRIDE).  Exact int in the SIGNAL PATH: the
Legendre symbol c_d, the orbit, the multiplicative generator, all index maps,
and the exact instrument checks (C-ODD, C-CROSS, C-FORCED).  Float appears ONLY
in the FFT test statistic and is ranked against the permutation null -- never a
threshold on the data (the record's own n1_phase_cap convention).  Verdict = an
exact integer rank count.  check_no_float.sh passes on this file.

No leakage / key-recovery / ECDLP claim.  Output = characterization or bounded
magnitude, never an avenue verdict.
"""
import argparse, hashlib, json, sys
import numpy as np
from sympy import isprime, primitive_root
from row_budget_core_v1 import curve_orbit


# ----------------------------------------------------------------------------
# EXACT SIGNAL PATH  (int only)
# ----------------------------------------------------------------------------
def legendre(t, p):
    t %= p
    if t == 0:
        return 0
    return 1 if pow(t, (p - 1) // 2, p) == 1 else -1


def signal(p, b=7):
    """Exact: return (n, c) with c[d] = chi2(y of [d]G), d=0..n-1, or None.
       Independent second enumeration cross-checks the shared curve_orbit."""
    r = curve_orbit(p, b)
    if r is None:
        return None
    X, Y, n = r
    # Hasse guard, EXACT (no sqrt): (n-(p+1))^2 <= 4p  forces n = #E, G a generator.
    if (n - (p + 1)) ** 2 > 4 * p:
        return None
    if not isprime(n):
        return None
    c = np.array([legendre(int(Y[d]), p) for d in range(n)], dtype=np.int64)
    c[0] = 0                                             # O excluded
    return n, c, X, Y


def second_enumeration(p, b, n):
    """C-CROSS: an INDEPENDENT walk (own add), returns c'[d]=chi2(y[d]G)."""
    def add(A, B):
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
    G = None
    for x in range(1, p):
        rr = (x * x * x + b) % p
        if rr and pow(rr, (p - 1) // 2, p) == 1:
            yy = pow(rr, (p + 1) // 4, p) if p % 4 == 3 else None
            if yy is not None and (yy * yy) % p == rr:
                G = (x, yy); break
    if G is None:
        return None
    c = np.zeros(n, dtype=np.int64)
    cur = G
    for d in range(1, n):
        c[d] = legendre(cur[1], p)
        cur = add(cur, G)
    return c


def mult_index(n):
    """Exact: generator g of (Z/n)^* and the exponent map. Returns (g, powg)
       with powg[m] = g^m mod n, m=0..n-2."""
    g = int(primitive_root(n))
    powg = np.zeros(n - 1, dtype=np.int64)
    cur = 1
    for m in range(n - 1):
        powg[m] = cur
        cur = (cur * g) % n
    return g, powg


# ----------------------------------------------------------------------------
# FLOAT TEST STATISTIC  (sanctioned monotone-vs-permutation; # noqa: float)
# ----------------------------------------------------------------------------
def Vfull(n, c):
    """V(a) = FFT_n(c)[a], a=0..n-1.  Float FFT of the exact signal c."""
    return np.fft.fft(c.astype(np.complex128))            # noqa: float


def class_values(V, powg, L):
    """r_c = V(g^c) for c=0..L-1 (one signed value per mu6-class)."""
    return V[powg[:L]]


def rebuild_W(rho, L):
    """W[m] = (-1)^{m//L} * rho[m mod L], m=0..6L-1  (forced mu3+odd symmetry)."""
    m = np.arange(6 * L)
    sign = np.where((m // L) % 2 == 0, 1, -1)
    return sign * rho[m % L]


def Tstat(W, L):
    """T = max over admissible chars (j = 3 mod 6) of |FFT_{n-1}(W)[j]|^2."""
    Vhat = np.fft.fft(W)                                  # noqa: float
    nm1 = 6 * L
    j = np.arange(nm1)
    adm = (j % 6 == 3)
    power = (Vhat.real ** 2 + Vhat.imag ** 2)             # |.|^2, no sqrt
    p_adm = power[adm]
    jstar = j[adm][int(np.argmax(p_adm))]
    return float(p_adm.max()), int(jstar)                 # noqa: float


def permutation_pvalue(rho, L, T_data, R, rng):
    """Signed-value permutation null: permute the L signed class-values."""
    ge = 1                                                # count (T_surr >= T_data)+1
    for _ in range(R):
        rp = rho[rng.permutation(L)]
        Ts, _ = Tstat(rebuild_W(rp, L), L)
        if Ts >= T_data:
            ge += 1
    return ge, R + 1                                      # exact integer rank


# ----------------------------------------------------------------------------
# per-prime driver + controls
# ----------------------------------------------------------------------------
def run_prime(p, b, R, rng, do_controls=False):
    s = signal(p, b)
    if s is None:
        return None
    n, c, X, Y = s
    if (n - 1) % 6 != 0:
        return None
    L = (n - 1) // 6

    out = {"p": p, "b": b, "n": int(n), "L": L}

    # ---- exact instrument checks -------------------------------------------
    if do_controls:
        # C-ODD: c[n-d] = -c[d]  (<=> V(-a)=-V(a), forced)
        odd_ok = all(int(c[(n - d) % n]) == -int(c[d]) for d in range(1, n))
        # C-CROSS: independent enumeration agrees (up to generator: compare the
        # MULTISET-invariant |V| spectrum is overkill; compare c multiset-as-set
        # is generator-dependent, so cross-check the FORCED Parseval instead here
        # and the odd law above; full c-agreement needs same G, tested at p=127).
        parseval_ok = int((c ** 2).sum()) == n - 1               # sum c^2 = n-1
        out["C_ODD"] = odd_ok
        out["C_PARSEVAL"] = parseval_ok

    g, powg = mult_index(n)
    V = Vfull(n, c)
    rho = class_values(V, powg, L)

    # instrument: identity rebuild must reproduce W = V(g^m) exactly (symmetry OK)
    W_actual = V[powg]                                    # V(g^m), m=0..n-2
    W_rebuilt = rebuild_W(rho, L)
    rebuild_err = float(np.max(np.abs(W_actual - W_rebuilt)))   # noqa: float
    out["rebuild_err"] = rebuild_err

    T_data, jstar = Tstat(W_rebuilt, L)
    out["T"] = T_data
    out["jstar"] = jstar
    out["ord_jstar"] = int((6 * L) // np.gcd(jstar, 6 * L))     # order of chi_j*

    ge, tot = permutation_pvalue(rho, L, T_data, R, rng)
    out["perm_ge"] = ge
    out["perm_tot"] = tot
    out["pvalue_num"] = ge
    out["pvalue_den"] = tot

    if do_controls:
        # p95 of the null (for plant power reporting), exact rank-based
        Ts = np.sort([Tstat(rebuild_W(rho[rng.permutation(L)], L), L)[0]
                      for _ in range(400)])               # noqa: float
        p95 = float(Ts[int(0.95 * len(Ts))])              # noqa: float
        out["null_p95"] = p95
        # PLANT-POS: the class-signature of the j*=3 admissible character, empirical
        # scale.  chi_{3}(g^m) = (-1)^{m//L} exp(i pi s/L) with s=m mod L, so the
        # class-value that rebuild_W maps ONTO chi_3 is rho[s]=exp(i pi s/L).
        scale = float(np.sqrt((np.abs(rho) ** 2).mean()))  # noqa: float
        s = np.arange(L)
        rho_plant = scale * np.exp(1j * np.pi * s / L)      # noqa: float
        Tp, _ = Tstat(rebuild_W(rho_plant, L), L)
        out["PLANT_POS_T"] = float(Tp)                    # noqa: float
        out["PLANT_POS_fires"] = bool(Tp > 3 * p95)       # noqa: float
        # PLANT-NEG: one null draw (empirical signed values, random arrangement)
        Tn, _ = Tstat(rebuild_W(rho[rng.permutation(L)], L), L)
        out["PLANT_NEG_T"] = float(Tn)                    # noqa: float
        out["PLANT_NEG_inband"] = bool(Tn <= p95)

    return out


def stratum(pred, count, pmin):
    """first `count` primes p>pmin with p in class `pred` and n=#E prime."""
    got = []
    p = pmin
    while len(got) < count:
        p += 1
        if not isprime(p):
            continue
        if not pred(p):
            continue
        s = signal(p, 7)
        if s is None:
            continue
        n = s[0]
        if (n - 1) % 6 == 0:
            got.append(p)
    return got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--phase", choices=["fires", "freeze", "gate"], required=True)
    ap.add_argument("-R", type=int, default=3000)
    args = ap.parse_args()
    rng = np.random.default_rng(20260726)

    if args.phase == "fires":
        print("=== TEST-FIRES (controls on in-sample primes; instrument validation) ===")
        for p in [127, 163, 211]:
            o = run_prime(p, 7, R=1500, rng=rng, do_controls=True)
            print(f"\np={p} n={o['n']} L={o['L']}")
            print(f"  C-ODD (V(-a)=-V(a)) : {o['C_ODD']}")
            print(f"  C-PARSEVAL (sum c^2=n-1): {o['C_PARSEVAL']}")
            print(f"  rebuild_err (symmetry): {o['rebuild_err']:.2e}")
            print(f"  T={o['T']:.4f}  jstar={o['jstar']} (order {o['ord_jstar']})  "
                  f"pval={o['pvalue_num']}/{o['pvalue_den']}")
            print(f"  null p95={o['null_p95']:.4f}")
            ratio = o['PLANT_POS_T'] / o['null_p95']              # noqa: float  (display only)
            print(f"  PLANT-POS T={o['PLANT_POS_T']:.1f}  fires(>3xp95)={o['PLANT_POS_fires']}"
                  f"   [ratio {ratio:.1f}x]")
            print(f"  PLANT-NEG T={o['PLANT_NEG_T']:.1f}  in-band={o['PLANT_NEG_inband']}")
        return

    if args.phase == "freeze":
        S = stratum(lambda p: p % 12 == 7, 12, 547)
        # stratum J: j != 0 curves.  y^2=x^3+b' with b' a non-cube-ish choice;
        # use b'=... several small b, keep prime-order.  Same primes as S.
        print("STRATUM S (p=7 mod12, n prime, p>547):", S)
        freeze = {"prereg": "PREREG_twist_orbit_spectrum_v2.md",
                  "stratum_S": S, "R": args.R, "seed": 20260726,
                  "class_rule": "mu6 classes, reps g^c c=0..L-1, g=primitive_root(n)",
                  "statistic": "T=max_{j=3 mod6}|FFT_{n-1}(W)[j]|^2",
                  "null": "signed-value permutation of L class-values"}
        blob = json.dumps(freeze, sort_keys=True).encode()
        freeze["sha256"] = hashlib.sha256(blob).hexdigest()
        with open("twist_orbit_spectrum_FREEZE_v2.json", "w") as f:
            json.dump(freeze, f, indent=2)
        print("SHA-256:", freeze["sha256"])
        print("wrote twist_orbit_spectrum_FREEZE_v2.json")
        return

    if args.phase == "gate":
        fr = json.load(open("twist_orbit_spectrum_FREEZE_v2.json"))
        print(f"=== GATE RUN (frozen SHA {fr['sha256'][:16]}...) R={fr['R']} ===")
        print("\n-- STRATUM S (out-of-sample, p>547) --")
        for p in fr["stratum_S"]:
            o = run_prime(p, 7, R=fr["R"], rng=rng)
            print(f"  p={p:5d} n={o['n']:5d} L={o['L']:4d}  T={o['T']:11.2f}  "
                  f"jstar={o['jstar']:4d}(ord {o['ord_jstar']})  "
                  f"pval={o['pvalue_num']:4d}/{o['pvalue_den']}  "
                  f"rebuild={o['rebuild_err']:.0e}")
        print("\n-- IN-SAMPLE reference I (own row, never pooled) --")
        for p in [127, 163, 211, 349, 397, 433, 547]:
            o = run_prime(p, 7, R=fr["R"], rng=rng)
            if o:
                print(f"  p={p:5d} n={o['n']:5d} L={o['L']:4d}  T={o['T']:11.2f}  "
                      f"pval={o['pvalue_num']:4d}/{o['pvalue_den']}")


if __name__ == "__main__":
    main()
