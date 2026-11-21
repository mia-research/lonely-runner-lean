#!/usr/bin/env python3
"""bandrep_r0dump_v1.py -- [25,29) D=1 fixed-R0 exact re-dump WITH FULL RECORDS (Track B).

Sibling of bandrep_gen_v1.py (r0 mode validated the counts in E916: 632,548 roots
reproduced, 555,170 exact-certified vs the C certifier's 541,537).  This sibling re-runs
the SAME exact certifier but DUMPS every certified record (root k-tuple, chosen scaled
clear point r = ceil(lo*BASE), per-reading gap indices j, and the feasible interval
[lo, hi] as exact fraction strings) so the compressed-template emitter
(bandrep_bulktab_v1.py) can consume per-root certificates and the certificate-shape
grouping can be measured.

Certificate semantics (E832 item 1, D = 1, base = 2^20): root k = 6-tuple over
rho_2..rho_7 (k7 in [25,29)), feasible R0 interval = intersection over readings of the
unions of per-lap intervals [(8j+1)/k_i, (8j+7)/(k_i+1)]; r = ceil(lo*BASE); the row is
kept iff r/BASE <= hi and every reading has a gap j_i with
(8j_i+1)*BASE <= r*k_i  and  r*(k_i+1) <= (8j_i+7)*BASE.
The rho_1 reading is pinned (= 1) by the E832 convention, so a row additionally needs
R0 = r/BASE in [1, 7] to be a BandFixedR0 (rho_1-pinned) instance; rows outside are
counted and reported (honest split of E916's 555,170 vs the C ledger's 541,537).

New-file discipline: sibling script; edits nothing existing.  All arithmetic exact.
Parallel: Pool over the 4 k7 values (each worker sweeps its tails, exact Fractions).
"""
import json, os, sys, time
from fractions import Fraction
from itertools import combinations_with_replacement
from multiprocessing import Pool

BASE = 1 << 20
N8 = os.path.dirname(os.path.abspath(__file__))


def _feasible_R0(k, D):
    """Exact feasible R0 set for a 6-tuple of cells (k, depth D): intersection over
    readings of the unions of per-lap intervals [(8j+1)D/k_i, (8j+7)D/(k_i+1)].
    Verbatim from bandrep_gen_v1.py r0 mode (the E916-validated instrument)."""
    def union(ki):
        out = []
        for j in range(0, (8 * ki + 7) // 8 + 2):
            lo = Fraction((8 * j + 1) * D, ki)
            hi = Fraction((8 * j + 7) * D, ki + 1)
            if lo <= hi:
                out.append((lo, hi))
        return out
    sets = [union(ki) for ki in k]
    best = None
    for lo0, hi0 in sets[0]:
        cur_lo, cur_hi = lo0, hi0
        ok = True
        for other in sets[1:]:
            frag = None
            for lo, hi in other:
                a, b = max(cur_lo, lo), min(cur_hi, hi)
                if a <= b and (frag is None or a < frag[0]):
                    frag = (a, b)
            if frag is None:
                ok = False
                break
            cur_lo, cur_hi = frag
        if ok and (best is None or cur_lo < best[0]):
            best = (cur_lo, cur_hi)
    return best


def sweep_k7(k7):
    """All roots with k7 fixed: returns (roots, certified, records) in sweep order."""
    roots = 0
    recs = []
    for tail in combinations_with_replacement(range(1, k7 + 1), 5):
        k = tuple(tail) + (k7,)
        roots += 1
        iv = _feasible_R0(k, 1)
        if iv is None:
            continue
        lo, hi = iv
        r = -((-lo.numerator * BASE) // lo.denominator)      # ceil(lo * BASE)
        # keep iff r/BASE <= hi (exact); mirrors the E916 r0-mode double check
        if Fraction(r, BASE) > hi:
            continue
        ok_j = []
        good = True
        for ki in k:
            found = None
            for j in range(0, (8 * ki + 7) // 8 + 2):
                if (8 * j + 1) * BASE <= r * ki and r * (ki + 1) <= (8 * j + 7) * BASE:
                    found = j
                    break
            if found is None:
                good = False
                break
            ok_j.append(found)
        if good:
            recs.append({"k": list(k), "r": r, "j": ok_j,
                         "lo": f"{lo.numerator}/{lo.denominator}",
                         "hi": f"{hi.numerator}/{hi.denominator}"})
    return roots, len(recs), recs


def main():
    t0 = time.time()
    out_path = os.path.join(N8, "bandrep_r0_redump_25_29_v1.jsonl")
    out_summary = os.path.join(N8, "bandrep_r0_redump_25_29_v1.out")
    with Pool(4) as p:
        results = p.map(sweep_k7, [25, 26, 27, 28])
    tot_roots = sum(rr for rr, _, _ in results)
    tot_cert = sum(nc for _, nc, _ in results)
    valid = 0
    below = above = 0
    with open(out_path, "w") as f:
        for k7, (roots, nc, recs) in zip([25, 26, 27, 28], results):
            for rec in recs:
                if rec["r"] < BASE:
                    below += 1
                elif rec["r"] > 7 * BASE:
                    above += 1
                else:
                    valid += 1
                f.write(json.dumps(rec) + "\n")
    lines = [
        f"# bandrep_r0dump_v1: [25,29) D=1 exact re-dump with records (E916 r0 instrument)",
        f"roots={tot_roots} (ledger: 632548)",
        f"certified={tot_cert} (E916 re-dump: 555170; C ledger: 541537)",
        f"rho1-pinned valid (BASE <= r <= 7*BASE): {valid}",
        f"r < BASE (R0 < 1, not a rho1-pinned instance): {below}",
        f"r > 7*BASE (R0 > 7, not a rho1-pinned instance): {above}",
        f"elapsed: {time.time()-t0:.1f} s",
    ]
    for ln in lines:
        print(ln, flush=True)
    with open(out_summary, "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
