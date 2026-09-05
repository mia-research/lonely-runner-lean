#!/usr/bin/env python3
"""
p0prime_rotation_law_v1.py -- is the sextic localization a LAW?

Cut 3 showed the low-mode excess concentrates on sextic classes chi6(b)/chi6(c)
of the frequency, and the 'special class' ROTATES per prime.  Hypothesis: the
per-prime excess-by-class 6-vector is a cyclic SHIFT of one common shape, and the
shift is fixed by an arithmetic invariant of the Frobenius (the a_p law's correct,
sextic-valued successor).

Gauge-free test via the 6-point DFT of the excess vector V=(e_0..e_5):
  |Vhat[k]|      shift-INVARIANT  -> the common SHAPE (which harmonics present)
  arg(Vhat[1])   shifts by (shift)*2pi/6 -> the per-prime ORIENTATION
If the vectors share a shape, |Vhat[k]| agrees across primes; the law is then
"arg(Vhat[1]) is a function of an arithmetic invariant".  We correlate the
orientation against candidate invariants (a_p mod 6, n mod 6, chi6(7)=the twist
parameter's sextic class, chi6(a_p), ...).

Two modes: default computes the 6-vectors (heavy) and dumps JSON; --analyze reads
the JSON and does the DFT + invariant correlation (fast, re-runnable).
Exact N_LOW counts; exploratory float statistics marked # noqa: float.
"""
import argparse, json, cmath, math
import numpy as np
from row_budget_run_v1 import load_freqs, mu6_orbits, Permuter, SPEC_N, SPEC_BETA
from row_budget_core_v1 import curve_orbit

THRESH = 0.01   # noqa: float
OUT = "p0prime_rotation_law_v1.json"


def sextic_class_arr(vals, p):
    from sympy import primitive_root
    z6 = pow(int(primitive_root(p)), (p - 1) // 6, p)
    roots = {}; x = 1
    for k in range(6):
        roots[x] = k; x = x * z6 % p
    return np.array([roots[pow(int(v) % p, (p - 1) // 6, p)] if v % p else -1
                     for v in vals], dtype=np.int64)


def excess_vectors(p, F, R, rng):
    X, Y, n = curve_orbit(p); assert n == SPEC_N[p]
    beta = SPEC_BETA[p]; xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    tab = np.exp(2j * np.pi * np.arange(p) / p)          # noqa: float
    B = np.array([b for b, c in F]); C = np.array([c for b, c in F])
    cb = sextic_class_arr(B, p); cc = sextic_class_arr(C, p)
    char = np.zeros(len(F), dtype=np.int64)
    null = np.zeros(len(F))                              # noqa: float
    for i, (b, c) in enumerate(F):
        e = (b * X + c * Y) % p
        s = tab[e]; s[0] = 0.0                           # noqa: float
        U2 = np.abs(np.fft.fft(np.array([s] + [s[P6.draw(rng)] for _ in range(R)]),
                               axis=1)) ** 2             # noqa: float
        low = (U2 / (n - 1))[:, 1:] < THRESH             # noqa: float
        char[i] = int(low[0].sum()); null[i] = low[1:].sum() / R   # noqa: float
    exc = char - null                                    # noqa: float
    def vec(cls):
        out = []
        for k in range(6):
            m = cls == k
            base = float(char[m].sum() - exc[m].sum())   # noqa: float
            out.append(float(exc[m].sum() / base) if base > 0 else 0.0)  # noqa: float
        return out
    return dict(p=p, n=int(n), a_p=int(p + 1 - n), e_b=vec(cb), e_c=vec(cc))


def dft6_phase(v):
    v = np.array(v) - np.mean(v)                          # noqa: float  drop DC
    Vh = np.fft.fft(v)                                    # noqa: float
    mags = [round(abs(Vh[k]), 4) for k in range(6)]       # noqa: float
    ph1 = math.degrees(cmath.phase(Vh[1])) % 360          # noqa: float
    dom = int(np.argmax(np.abs(Vh[1:4])) + 1)             # dominant harmonic 1..3
    return mags, ph1, dom


def analyze():
    data = json.load(open(OUT))
    from sympy import primitive_root
    print(f"{'p':>6} {'a_p':>5} {'ap%6':>4} {'chi6(7)':>7} | "
          f"{'axis':>4} {'domH':>4} {'|Vh1|':>6} {'arg(Vh1)deg':>11}")
    for axis in ("e_c", "e_b"):
        print(f"\n== axis {axis} ==")
        rows = []
        for d in data:
            p = d["p"]
            c67 = pow(7, (p - 1) // 6, p)
            # class of chi6(7): match to zeta6^k
            z6 = pow(int(primitive_root(p)), (p - 1) // 6, p)
            cls7 = next(k for k in range(6) if pow(z6, k, p) == c67 % p)
            mags, ph1, dom = dft6_phase(d[axis])
            rows.append((p, d["a_p"], d["a_p"] % 6, cls7, dom, mags[1], ph1))
            print(f"{p:>6} {d['a_p']:>5} {d['a_p']%6:>4} {cls7:>7} | "
                  f"{axis:>4} {dom:>4} {mags[1]:>6.3f} {ph1:>11.1f}")
        # is arg(Vh1) (as a class 0..5) a function of a_p%6 or chi6(7)?
        ph_class = [int(round(r[6] / 60)) % 6 for r in rows]  # noqa: float phase->0..5
        for name, idx in (("a_p%6", 2), ("chi6(7)", 3), ("domH", 4)):
            vals = [r[idx] for r in rows]
            # exact test: how many distinct (predictor -> ph_class) collisions
            mp = {}
            ok = True
            for v, pc in zip(vals, ph_class):
                if v in mp and mp[v] != pc:
                    ok = False
                mp.setdefault(v, pc)
            print(f"    orientation vs {name}: {'FUNCTIONAL (no collision)' if ok else 'not a clean function'}"
                  f"  map={mp}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349,433,577,991,2089,4159,9319,19231")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--seed", type=int, default=20260831)
    ap.add_argument("--analyze", action="store_true")
    a = ap.parse_args()
    if a.analyze:
        analyze(); return
    freqs, h = load_freqs()
    rng = np.random.default_rng(a.seed)
    out = []
    import time
    for p in [int(t) for t in a.primes.split(",")]:
        t0 = time.time()
        out.append(excess_vectors(p, freqs[p], a.R, rng))
        json.dump(out, open(OUT, "w"), indent=1)
        print(f"  p={p} done [{int(time.time()-t0)}s]  e_c={[round(x,3) for x in out[-1]['e_c']]}")
    print(f"wrote {OUT}; run with --analyze")


if __name__ == "__main__":
    main()
