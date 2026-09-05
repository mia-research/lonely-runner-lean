#!/usr/bin/env python3
"""
arm4_stage2_calibration_v1.py — ARM 4 stage 2: the null ensemble and the plant
sweep, computed and HASHED BEFORE the primary statistic is ever evaluated on the
true pairing (spec section 5.1 ordering rule).

Writes arm4_calibration_v1.json and prints its sha256.  Stage 3 asserts that hash.

Nothing in this file evaluates T_4 on the true pairing.
"""
import json, hashlib
import numpy as np

ZETA6 = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]
DIAG = [(j, (-j) % 6) for j in range(1, 6)]                      # df = 5
EVEN = [(j, k) for j in range(6) for k in range(6) if (j + k) % 2 == 0]
OFF = [(j, k) for (j, k) in EVEN if (j, k) != (0, 0) and k != (-j) % 6]  # df = 12
ODD = [(j, k) for j in range(6) for k in range(6) if (j + k) % 2 == 1]   # forced 0
assert len(DIAG) == 5 and len(OFF) == 12 and len(ODD) == 18


def table_of(u, w):
    return np.bincount(u.astype(np.int64) * 6 + w.astype(np.int64),
                       minlength=36).reshape(6, 6)


def U(tab, j, k):
    A = B = 0
    for a in range(6):
        for b in range(6):
            c = int(tab[a, b])
            if not c: continue
            zu, zv = ZETA6[(j * a + k * b) % 6]
            A += c * zu; B += c * zv
    return A * A - A * B + B * B          # |U|^2, exact integer


def stats(tab):
    return (sum(U(tab, j, k) for j, k in DIAG),
            sum(U(tab, j, k) for j, k in OFF),
            sum(U(tab, j, k) for j, k in ODD))


def paired_table(su_p, su_n, sw_p, sw_n, perm, eps):
    """Pair-permutation null: pi(+d_i) = +eps_i d_sigma(i), pi(-d_i) = -eps_i d_sigma(i)."""
    wp = np.where(eps > 0, sw_p[perm], sw_n[perm])
    wn = np.where(eps > 0, sw_n[perm], sw_p[perm])
    return table_of(np.concatenate([su_p, su_n]), np.concatenate([wp, wn]))


def main():
    d = np.load("arm4_features_v1.npz")
    su_p, su_n = d["su_p"], d["su_n"]; sw_p, sw_n = d["sw_p"], d["sw_n"]
    K0 = len(su_p); rng = np.random.default_rng(20260724)

    # ---------------- primary null ensemble, B = 999
    B = 999
    T4n = []; Toffn = []; broke = 0
    for _ in range(B):
        perm = rng.permutation(K0)
        eps = rng.integers(0, 2, K0) * 2 - 1
        t4, toff, todd = stats(paired_table(su_p, su_n, sw_p, sw_n, perm, eps))
        if todd != 0: broke += 1
        T4n.append(int(t4)); Toffn.append(int(toff))
    print(f"  null ensemble B={B}: draws that BROKE a forced zero = {broke}")
    print(f"    (spec 4.4: any breakage means the null is mis-built and voids the arm)")
    T4n = np.array(T4n, dtype=float); Toffn = np.array(Toffn, dtype=float)
    print(f"    T_4   null: median {np.median(T4n):.4g}  99th pct {np.quantile(T4n,0.99):.4g}")
    print(f"    T_off null: median {np.median(Toffn):.4g}  99th pct {np.quantile(Toffn,0.99):.4g}")

    # ---------------- plant sweep: must fire, or the arm is void
    print(f"\n  PLANT SWEEP (copy s_u <- s_w on a fraction eps of antipodal pairs)")
    plant = {}
    for e in (0.001, 0.002, 0.005, 0.01, 0.02):
        hits = 0
        for _ in range(20):
            m = rng.random(K0) < e
            pu_p = np.where(m, sw_p, su_p)
            pu_n = np.where(m, (sw_p.astype(int) + 3) % 6, su_n).astype(np.uint8)
            t4o, _, _ = stats(table_of(np.concatenate([pu_p, pu_n]),
                                       np.concatenate([sw_p, sw_n])))
            # fresh small null built FROM THE PLANTED DATA (B=99)
            nul = []
            for _ in range(99):
                pm = rng.permutation(K0); ep = rng.integers(0, 2, K0) * 2 - 1
                t4b, _, _ = stats(paired_table(pu_p, pu_n, sw_p, sw_n, pm, ep))
                nul.append(t4b)
            if (1 + sum(1 for x in nul if x >= t4o)) / 100.0 <= 0.01:
                hits += 1
        plant[str(e)] = hits
        print(f"    eps={e:<6} rejects at alpha=0.01 in {hits}/20 draws")
    fired = [float(e) for e, h in plant.items() if h >= 18]
    estar = min(fired) if fired else None
    print(f"\n  FIRING CRITERION (>=18/20): "
          f"{'FIRES at eps* = ' + str(estar) if estar else 'DOES NOT FIRE -> ARM 4 VOID'}")

    out = dict(K0=int(K0), B=B, T4_null=[int(x) for x in T4n],
               Toff_null=[int(x) for x in Toffn], plant=plant,
               eps_star=estar, forced_broken_draws=int(broke))
    with open("arm4_calibration_v1.json", "w") as f:
        json.dump(out, f, sort_keys=True)
    h = hashlib.sha256(open("arm4_calibration_v1.json", "rb").read()).hexdigest()
    print(f"\n  calibration written: arm4_calibration_v1.json")
    print(f"  sha256 = {h}")


if __name__ == "__main__":
    main()
