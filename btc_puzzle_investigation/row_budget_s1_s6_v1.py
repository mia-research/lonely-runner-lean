#!/usr/bin/env python3
"""
row_budget_s1_s6_v1.py — the two secondaries of PREREG_row_budget_lowtail_v1.md
section 3.3 that the v1 run did not execute (deviations D3, D4).

  S1  Theta_p = Spearman rank corr across f between N_LOW(f) and
      B_HIGH(f) := (1/n) sum_{a != 0, r > 1.5} rho(a;f),  integer mid-ranks,
      compared to the MN-mu6 replicate distribution {Theta^{(r)}} by rank.
      v1 calls this the ONLY statistic in the design that is not an additive
      marginal -- i.e. the only one F5 does not render uninformative on the
      character side.  A large POSITIVE coupling is forced in BOTH arms by the
      fixed budget; only the char-minus-null DIFFERENCE is read.

  S6  the primary recomputed on the c=0 and b=0 strata separately, with
      MN-mu6 and MN-neg only.  F7: a free shuffle is an INVALID null on the
      special strata (it destroys a symmetry they have by definition), so
      MN-free is not run here, and the strata are never pooled with the generic.

ORDERING, stated plainly: both statistics and both formulas were frozen in the
v1 spec BEFORE any data was seen; they are executed now only because v1 skipped
them.  Both are declared in that spec as "reported, never verdict-bearing on
their own".  **The v1 verdict remains ABSTAIN (outcome O6, planted control did
not fire) and nothing here revives it.**
"""
import argparse, hashlib, json
import numpy as np
from row_budget_core_v1 import curve_orbit
from row_budget_run_v1 import (load_freqs, mu6_orbits, neg_orbits, Permuter,
                               SPEC_N, SPEC_BETA, THRESH)

SPECIAL = "PREREG_row_budget_lowtail_v1_FREQS_SPECIAL.txt"
SPECIAL_SHA = "dfa9f7a40d27a03f906e9fb03d6466775b980b28c62a04e6675792124811ee9e"
HIGH = 2.25                     # r > 1.5  <=>  rho > 2.25


def load_special():
    raw = open(SPECIAL, "rb").read()
    h = hashlib.sha256(raw).hexdigest()
    assert h == SPECIAL_SHA, f"SPECIAL HASH MISMATCH {h}"
    cz, bz = {}, {}
    for line in raw.decode().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        p, b, c = (int(t) for t in line.split())
        (cz if c == 0 else bz).setdefault(p, []).append((b, c))
    return cz, bz, h


def midranks(v):
    """average (mid) ranks, ties averaged — integer-exact ordering, no float cmp."""
    n = len(v)
    order = np.argsort(v, kind="mergesort")
    sv = v[order]
    r = np.empty(n, dtype=float)
    i = 0
    while i < n:
        j = i
        while j + 1 < n and sv[j + 1] == sv[i]:
            j += 1
        r[order[i:j + 1]] = 0.5 * (i + j) + 1.0
        i = j + 1
    return r


def spearman(a, b):
    ra, rb = midranks(a), midranks(b)
    ra -= ra.mean(); rb -= rb.mean()
    den = np.sqrt((ra * ra).sum() * (rb * rb).sum())
    return float((ra * rb).sum() / den) if den > 0 else float("nan")


def setup(p):
    X, Y, n = curve_orbit(p)
    assert n == SPEC_N[p]
    beta = SPEC_BETA[p]
    xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    assert int(np.max((X[(lam * np.arange(n)) % n] - beta * X) % p)) == 0
    r6 = mu6_orbits(n, lam); r2 = neg_orbits(n)
    return X, Y, n, Permuter(n, *r6), Permuter(n, *r2)


def stats_for(p, F, R, rng, nulls=("mu6",)):
    """per-frequency N_LOW and B_HIGH for char and each null replicate."""
    X, Y, n, P6, P2 = setup(p)
    tab = np.exp(2j * np.pi * np.arange(p) / p)
    m = len(F)
    NL_c = np.zeros(m); BH_c = np.zeros(m)
    NL_n = {k: np.zeros((R, m)) for k in nulls}
    BH_n = {k: np.zeros((R, m)) for k in nulls}
    perm = {"mu6": P6, "neg": P2}
    for i, (b, c) in enumerate(F):
        e = (b * X + c * Y) % p
        s = tab[e]; s[0] = 0.0
        rows = [s]
        for k in nulls:
            for _ in range(R):
                rows.append(s[perm[k].draw(rng)])
        U2 = np.abs(np.fft.fft(np.array(rows), axis=1)) ** 2
        rho = U2 / (n - 1)
        nl = (rho[:, 1:] < THRESH).sum(1)
        bh = np.where(rho[:, 1:] > HIGH, rho[:, 1:], 0.0).sum(1) / n
        NL_c[i] = nl[0]; BH_c[i] = bh[0]
        off = 1
        for k in nulls:
            NL_n[k][:, i] = nl[off:off + R]; BH_n[k][:, i] = bh[off:off + R]
            off += R
    return NL_c, BH_c, NL_n, BH_n, n, m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349,433,577,991,2089,4159,9319,19231")
    ap.add_argument("--R", type=int, default=64)
    ap.add_argument("--out", default="row_budget_s1_s6_v1.json")
    a = ap.parse_args()
    freqs, _ = load_freqs()
    cz, bz, hsp = load_special()
    print(f"  SPECIAL list sha256 {hsp[:24]}...  OK")
    rng = np.random.default_rng(int(20260726))
    rows = []

    print("\n" + "=" * 92)
    print("S1 — Spearman coupling N_LOW(f) vs B_HIGH(f); only char MINUS null is read")
    print("=" * 92)
    print(f"{'p':>7} {'Theta_char':>11} {'Theta_mu6':>11} {'sd':>8} {'z':>8} {'rank-p':>8}")
    for p in [int(t) for t in a.primes.split(",")]:
        NL_c, BH_c, NL_n, BH_n, n, m = stats_for(p, freqs[p], a.R, rng, ("mu6",))
        th_c = spearman(NL_c, BH_c)
        th_n = np.array([spearman(NL_n["mu6"][r], BH_n["mu6"][r]) for r in range(a.R)])
        z = (th_c - th_n.mean()) / th_n.std(ddof=1)
        rk = (1 + int((np.abs(th_n - th_n.mean()) >= abs(th_c - th_n.mean())).sum())) / (a.R + 1.0)
        print(f"{p:>7} {th_c:>+11.4f} {th_n.mean():>+11.4f} {th_n.std(ddof=1):>8.4f} "
              f"{z:>+8.2f} {rk:>8.4f}")
        rows.append(dict(kind="S1", p=p, n=n, m=m, theta_char=th_c,
                         theta_null=float(th_n.mean()), sd=float(th_n.std(ddof=1)),
                         z=float(z), rank_p=rk))
        json.dump(rows, open(a.out, "w"), indent=1)

    print("\n" + "=" * 92)
    print("S6 — special strata, MN-mu6 and MN-neg only (F7: free shuffle INVALID here)")
    print("=" * 92)
    print(f"{'stratum':>8} {'p':>7} {'m':>6} {'char':>10} {'MN-mu6':>10} {'MN-neg':>10} {'z(mu6)':>9}")
    for nm, lst in (("c=0", cz), ("b=0", bz)):
        for p in [int(t) for t in a.primes.split(",")]:
            F = lst.get(p, [])
            if not F: continue
            NL_c, _, NL_n, _, n, m = stats_for(p, F, a.R, rng, ("mu6", "neg"))
            c_bar = NL_c.mean()
            m6 = NL_n["mu6"].mean(1); ng = NL_n["neg"].mean(1)
            z = (c_bar - m6.mean()) / m6.std(ddof=1)
            print(f"{nm:>8} {p:>7} {m:>6} {c_bar:>10.3f} {m6.mean():>10.3f} "
                  f"{ng.mean():>10.3f} {z:>+9.2f}")
            rows.append(dict(kind="S6", stratum=nm, p=p, n=n, m=m,
                             char=float(c_bar), mu6=float(m6.mean()),
                             neg=float(ng.mean()), z=float(z)))
            json.dump(rows, open(a.out, "w"), indent=1)

    print("\n  REMINDER: v1's verdict is ABSTAIN (O6). Neither S1 nor S6 is verdict-bearing.")


if __name__ == "__main__":
    main()
