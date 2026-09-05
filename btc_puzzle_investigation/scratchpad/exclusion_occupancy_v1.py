#!/usr/bin/env python3
"""
exclusion_occupancy_v1.py — the NEGATIVE/exclusion question, gate-free at POPULATED granularity.
Fence premise: no wall; a scoped null is scoped, never "impossible".

An empty cell (V=v, d mod k = r) that is NOT sampling-empty (cells well-populated: |V|*k << n) and NOT
forced by phi-symmetry = a HARD exclusion (observing V=v proves d != r), bits removed = per-v killed
residues. Power point (from the gate before it died): with big joint V, |V|*k > n => all cells sampling-
empty, meaningless. So test SMALL V. NOTE all five invariants are mu6-covariant (eps/chi2y/s-band phi-
invariant; chi3 +1, sextant +2 under phi) => the GLV orbit adds NO invariant info (mu6-saturation).

Signal path exact int. Occupancy counts are integers; no float verdict.
"""
from collections import Counter
from eps_to_d_run_v1 import prime_order_curve, full_orbit, padd, find_glv, chi3_index
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm, sextant as sxt_uv


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)


def invariants(p, m, G):
    xs = full_orbit(G, p, m)
    ys = [None] * m; acc = None
    for d in range(1, m):
        acc = padd(acc, G, p); ys[d] = acc[1]
    lam, beta, wp = find_glv(xs, p, m)
    eis, eps = build(p)

    def sband(x):
        E = enorm(eis(x))
        return 0 if 16 * E < 3 * p else (1 if 16 * E < 6 * p else 2)

    V = {}
    for name, f in [("chi3", lambda d: chi3_index(xs[d], p, wp)),
                    ("eps", lambda d: eps(xs[d])),
                    ("sextant", lambda d: sxt_uv(*eis(xs[d]))),
                    ("chi2y", lambda d: 1 if legendre(ys[d], p) == 1 else 0),
                    ("sband", lambda d: sband(xs[d]))]:
        V[name] = [f(d) for d in range(1, m)]
    dmod = {k: [d % k for d in range(1, m)] for k in (2, 3, 4, 6, 7)}
    return V, dmod, m - 1


def test_combo(feat_vals, r_vals, N):
    """occupancy of (feature, residue); return (#cells, #empty, min_occ, exp, hard_excl_bits)."""
    cells = Counter(zip(feat_vals, r_vals))
    fv = sorted(set(feat_vals)); rv = sorted(set(r_vals))
    ncells = len(fv) * len(rv)
    empty = ncells - len(cells)
    minocc = min(cells.values()) if cells else 0
    exp = N / ncells
    # bits removed: for each observed feature value v, which residues are IMPOSSIBLE (count 0)?
    killed = 0; total_v = 0
    for v in fv:
        present = {r for (vv, r) in cells if vv == v}
        if len(present) < len(rv):
            killed += (len(rv) - len(present))
        total_v += 1
    return ncells, empty, minocc, exp, killed, len(rv)


def main():
    print("Exclusion / empty-cell occupancy at POPULATED granularity (|V|*k << n). Fence premise.\n")
    for (lo, hi) in [(2089, 2090), (1303, 1304)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, m, G = r
        V, dmod, N = invariants(p, m, G)
        print(f"=== p={p} m={m} (N={N} keys) ===")
        print(f"  {'feature':>20} {'k':>2} {'cells':>5} {'empty':>5} {'min_occ':>7} {'exp':>6} {'killed-res':>10}")
        combos = [("chi3", ["chi3"]), ("eps", ["eps"]), ("sextant", ["sextant"]),
                  ("chi2y", ["chi2y"]), ("sband", ["sband"]),
                  ("chi3+chi2y", ["chi3", "chi2y"]), ("sextant+chi2y", ["sextant", "chi2y"]),
                  ("chi3+eps+chi2y", ["chi3", "eps", "chi2y"])]
        for cname, feats in combos:
            for k in (2, 3, 4, 6, 7):
                fv = list(zip(*[V[f] for f in feats])) if len(feats) > 1 else V[feats[0]]
                nc, empty, mino, exp, killed, nres = test_combo(fv, dmod[k], N)
                if nc > N // 5:            # keep cells populated (exp >= 5); skip over-fine
                    continue
                flag = "  <-- EMPTY (check forced)" if (empty > 0 and mino == 0 and exp >= 5) else ""
                print(f"  {cname:>20} {k:>2} {nc:>5} {empty:>5} {mino:>7} {exp:>6.1f} "
                      f"{killed:>4}/{nres:<5}{flag}")
        print()
    print("Read: empty=0 at exp>=5 => no HARD exclusion at that granularity (scoped, populated).")
    print("empty>0 with exp>=5 => candidate hard exclusion -> check if phi-forced before any claim.")


if __name__ == "__main__":
    main()
