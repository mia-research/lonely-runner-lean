#!/usr/bin/env python3
"""
formal_group_shadow_order2_run_v1.py -- THE RUN for PREREG_formal_group_shadow_order2_v1.md.

Executes the pre-registered spec verbatim: primary statistic rho_V, nulls N1/N2/N3,
controls C1-C4, graded plant P2 (m*), across the 12 pre-registered prime windows.

  rho_V = Xi_V / Xi_max ,  Xi_V = [(1/(p-1)) sum_b |W_V(b)|^4]^(1/4) ,
  W_V(b) = sum_{d=1}^{n-1} e_n(d) e_p(b V_d) ,  Xi_max = (n-1)/(p-1)^(1/4).

DECISION RULE (prereg 8): H_FG survives only if rho_{V2} exceeds the N2 decoy 95th pct
in >= 8 of 12 primes. rho_{V2} > rho_{V1} on its own decides NOTHING (prereg 9(0)).

FLOAT CARVE-OUT: curve arithmetic + readouts exact modular int; numpy float only in the
character-sum magnitudes (analytic size), never as a threshold on data.
"""
import math
import sys

import numpy as np

from t_y_maxbound_v1 import prime_order_curve, group_coords

SEED = 20260719
WINDOWS = [(150, 250), (250, 400), (400, 550), (550, 750), (750, 1100), (1100, 1500),
           (1500, 1900), (1900, 2500), (2500, 3200), (3200, 4200), (4200, 5500), (5500, 7000)]
N_DECOY = 200
B = 7


# ---------------- primary statistic ----------------
def rho(V, n, p):
    """V: int array length n (index 0 unused). Pooled 4th-moment alignment, prereg 2."""
    H = np.zeros(p, dtype=complex)
    w = np.exp(2j * np.pi * np.arange(1, n) / n)
    np.add.at(H, np.asarray(V[1:], dtype=np.int64) % p, w)
    W = np.fft.fft(H)
    m4 = float(np.mean(np.abs(W[1:]) ** 4))          # b = 1..p-1
    Xi = m4 ** 0.25
    return Xi / ((n - 1) / (p - 1) ** 0.25)


# ---------------- readouts (exact modular int) ----------------
def readouts(xs, ys, p, n):
    inv = lambda t: pow(t, p - 2, p)
    R1 = [0] * n
    for d in range(1, n):
        R1[d] = xs[d] * inv(ys[d]) % p            # x/y, the note's R^(1)
    R2 = [0] * n
    for d in range(1, n):
        R2[d] = (R1[d] + 3 * pow(R1[d], 7, p)) % p
    return R1, R2


def literal_R2(xs, ys, p, n):
    """The note's WRITTEN form, for control C3."""
    inv = lambda t: pow(t, p - 2, p)
    out = [0] * n
    for d in range(1, n):
        x, y = xs[d], ys[d]
        out[d] = x * inv(y) % p * (1 + 3 * pow(x, 6, p) * inv(pow((pow(x, 3, p) + B) % p, 3, p))) % p
    return out


def decoy(R1, p, n, c, k):
    return [0] + [(R1[d] + c * pow(R1[d], k, p)) % p for d in range(1, n)]


# ---------------- nulls ----------------
def n1_sample(V, n, p, rng):
    """Sign-preserving pair permutation: preserves V(-d) = -V(d) oddness."""
    h = (n - 1) // 2
    idx = rng.permutation(h) + 1
    signs = rng.choice([1, -1], size=h)
    out = np.zeros(n, dtype=np.int64)
    src = np.asarray(V, dtype=np.int64)
    vals = (signs * src[idx]) % p
    out[1:h + 1] = vals
    out[n - 1:n - h - 1:-1] = (-vals) % p
    return out


# ---------------- controls ----------------
def c1_plant(n, p):
    """Perfect cheap leak: L_d = ((dbar*p)//n) mod p, odd in d. Must read rho ~ 1.000."""
    L = [0] * n
    for d in range(1, n):
        db = d if d <= n // 2 else d - n
        L[d] = (db * p) // n % p
    return L


def c2_floor(n, p, rng):
    h = (n - 1) // 2
    v = rng.integers(0, p, size=h)
    out = np.zeros(n, dtype=np.int64)
    out[1:h + 1] = v
    out[n - 1:n - h - 1:-1] = (-v) % p
    return out


def p2_power(Vbase, L, n, p, rng, null95, reps=20):
    """Graded plant: m* = smallest m with rho > N1 95th pct in >= 18/20 reps."""
    h = (n - 1) // 2
    base = np.asarray(Vbase, dtype=np.int64)
    Lz = np.asarray(L, dtype=np.int64)
    for m in (0.01, 0.02, 0.05, 0.10, 0.20, 0.35, 0.50, 0.75, 1.0):
        hits = 0
        for _ in range(reps):
            V = base.copy()
            S = rng.choice(np.arange(1, h + 1), size=max(1, int(m * h)), replace=False)
            V[S] = Lz[S]
            V[n - S] = (-Lz[S]) % p
            if rho(V, n, p) > null95:
                hits += 1
        if hits >= 18:
            return m
    return None


# ---------------- glv control C4 ----------------
def c4_glv(xs, ys, p, n, R1, R2):
    e = (p - 1) // 3
    g = 2
    while pow(g, e, p) == 1:
        g += 1
    beta = pow(g, e, p)
    # find lambda from data: x_{lam*d} = beta*x_d  -> lam = index of the point (beta*x_1, y_1)
    target = (beta * xs[1] % p, ys[1])
    lam = None
    for d in range(1, n):
        if (xs[d], ys[d]) == target:
            lam = d
            break
    if lam is None:
        return None, None, False
    ok = all(R1[lam * d % n] == beta * R1[d] % p and R2[lam * d % n] == beta * R2[d] % p
             for d in range(1, min(n, 300)))
    return beta, lam, ok


def main():
    rng = np.random.default_rng(SEED)
    rows = []
    print("PREREG_formal_group_shadow_order2_v1 -- THE RUN\n")
    print(f"{'p':>6} {'n':>6} | {'C1':>6} {'C2flr':>6} {'C3':>3} {'C4':>3} | "
          f"{'rhoV1':>6} {'rhoV2':>6} | {'N1_95':>6} {'N2_95':>6} {'N3_95':>6} | "
          f"{'V2>N2?':>6} {'m*':>5}")
    for lo, hi in WINDOWS:
        got = prime_order_curve(lo, hi)
        if got is None:
            print(f"  [{lo},{hi}] no prime-order curve")
            continue
        p, n, G = got
        xs, ys = group_coords(G, p, n, 0)
        R1, R2 = readouts(xs, ys, p, n)

        # C3 exactness
        c3 = all(a == b for a, b in zip(literal_R2(xs, ys, p, n)[1:], R2[1:]))
        # C4 glv
        beta, lam, c4 = c4_glv(xs, ys, p, n, R1, R2)
        # C1 plant
        L = c1_plant(n, p)
        c1 = rho(L, n, p)
        # C2 floor
        c2 = float(np.mean([rho(c2_floor(n, p, rng), n, p) for _ in range(20)]))

        r1, r2 = rho(R1, n, p), rho(R2, n, p)

        n1 = np.array([rho(n1_sample(R2, n, p, rng), n, p) for _ in range(N_DECOY)])
        # N2: decoys t + c t^k, k = 1 mod 6, 7 <= k <= p-2, (c,k) != (3,7)
        n2v = []
        while len(n2v) < N_DECOY:
            k = int(rng.integers(1, (p - 2 - 1) // 6 + 1)) * 6 + 1
            c = int(rng.integers(1, p))
            if (c, k) == (3, 7) or k > p - 2:
                continue
            n2v.append(rho(decoy(R1, p, n, c, k), n, p))
        n2 = np.array(n2v)
        # N3: k odd, k != 1 mod 6
        n3v = []
        while len(n3v) < N_DECOY:
            k = int(rng.integers(1, p - 2))
            if k % 2 == 0 or k % 6 == 1:
                continue
            n3v.append(rho(decoy(R1, p, n, int(rng.integers(1, p)), k), n, p))
        n3 = np.array(n3v)

        n1_95, n2_95, n3_95 = (float(np.percentile(a, 95)) for a in (n1, n2, n3))
        beat = r2 > n2_95
        mstar = p2_power(R2, L, n, p, rng, n1_95)

        rows.append(dict(p=p, n=n, c1=c1, c2=c2, c3=c3, c4=c4, r1=r1, r2=r2,
                         n1=n1_95, n2=n2_95, n3=n3_95, beat=beat, m=mstar,
                         n2med=float(np.median(n2))))
        print(f"{p:>6} {n:>6} | {c1:>6.3f} {c2:>6.3f} {str(c3)[0]:>3} {str(c4)[0]:>3} | "
              f"{r1:>6.3f} {r2:>6.3f} | {n1_95:>6.3f} {n2_95:>6.3f} {n3_95:>6.3f} | "
              f"{str(beat):>6} {str(mstar):>5}")
        sys.stdout.flush()

    if not rows:
        return
    print("\n=== PRE-COMMITTED DECISION (prereg 8, 9) ===")
    print(f"  C1 plant: min {min(r['c1'] for r in rows):.3f} "
          f"(must be >= 0.99 or NOTHING is reportable)")
    print(f"  C3 exactness all pass: {all(r['c3'] for r in rows)}    "
          f"C4 GLV all pass: {all(r['c4'] for r in rows)}")
    nb = sum(1 for r in rows if r['beat'])
    print(f"  rho_V2 beats N2 decoy 95th pct in {nb}/{len(rows)} primes "
          f"(H_FG needs >= 8)  ->  H_FG {'SURVIVES' if nb >= 8 else 'FALSIFIED'} "
          f"in the basis-alignment reading")
    up = sum(1 for r in rows if r['r2'] > r['r1'])
    print(f"  [the note's own criterion, explicitly NOT decisive]: rho_V2 > rho_V1 in "
          f"{up}/{len(rows)} primes")
    print(f"  mean rho_V1 {np.mean([r['r1'] for r in rows]):.3f} | "
          f"mean rho_V2 {np.mean([r['r2'] for r in rows]):.3f} | "
          f"mean N2 decoy median {np.mean([r['n2med'] for r in rows]):.3f} | "
          f"mean C2 floor {np.mean([r['c2'] for r in rows]):.3f}")
    ms = [r['m'] for r in rows if r['m'] is not None]
    print(f"  m* (detection threshold) measured on {len(ms)}/{len(rows)} primes; "
          f"range {min(ms) if ms else '-'} .. {max(ms) if ms else '-'}")


if __name__ == '__main__':
    main()
