"""audit92_pinchreach.py -- reach of the two shared-lemma candidates over the
whole 5,772-control population and the 73 chain-box embeddings, by control
label.  A candidate "fires" on a control when its hypothesis (a self-contained
exact inequality test on (core, d)) holds; every fire must carry the verdict
'not common rejection' (soundness), and the pinch's fire set is the claimed
exclusive family.  Exact Fractions; output audit92_pinchreach.out (new).
"""
import importlib.util
import json
import os
import sys
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement
from math import floor
from random import Random

HERE = os.path.dirname(os.path.abspath(__file__))
N8 = os.path.dirname(HERE)

spec = importlib.util.spec_from_file_location(
    "cascade_anchor_audit", os.path.join(HERE, "audit92_anchor_lib.py"))
anchor = importlib.util.module_from_spec(spec)
sys.modules["cascade_anchor_audit"] = anchor
spec.loader.exec_module(anchor)
sys.path.insert(0, HERE)
import cascade_rejection_audit as cra  # noqa: E402

R = cra.R
clear_cells = cra.clear_cells
incompatible = cra.incompatible


def pinch_fires(core, d, cells):
    w = max(core)
    if not (Q(145, 21) <= w <= 7 and d >= w):
        return False
    if not all(Q(1) <= q <= 5 for q in core if q != w):
        return False
    P1 = (Q(1, 8), Q(7) / (8 * w))
    P2 = (Q(9) / (8 * w), Q(7, 40))
    if not all(any(A <= p and q <= B for A, B in cells) for p, q in (P1, P2)):
        return False
    return incompatible(d, P1, P2)


def binders(v, core):
    out = []
    for rho in core:
        t = v * rho - Q(1, 8)
        if t.denominator == 1 and t >= 0:
            out.append((rho, int(t), "entry"))
        t = v * rho - Q(7, 8)
        if t.denominator == 1 and t >= 0:
            out.append((rho, int(t), "exit"))
    return out


def seam_scissors_fires(core, d, cells):
    """Some j=0 incompatible pair with inner seam (b,c = one blocked zone of
    one reading) and scissors outer (a,e = one clear zone of one reading),
    with both reduced ratio conditions d <= 3 rho_i and d >= rho_o / 3."""
    for A, B in combinations(cells, 2):
        a, b, c, e = A[0], A[1], B[0], B[1]
        if floor(d * (e - a) - Q(1, 4)) != 0:
            continue
        se = [(rb, lb) for rb, lb, kb in binders(b, core) if kb == "exit"
              for rc, lc, kc in binders(c, core)
              if kc == "entry" and rb == rc and lc == lb + 1]
        if not se:
            continue
        sc = [(ra, la) for ra, la, ka in binders(a, core) if ka == "entry"
              for re_, le, ke in binders(e, core)
              if ke == "exit" and ra == re_ and le == la]
        if sc and d <= 3 * se[0][0] and d >= sc[0][0] / 3:
            return True
    return False


def main():
    out = []

    def emit(s=""):
        out.append(s)
        print(s, flush=True)

    rng = Random(8)
    cores = [(1, *c) for c in combinations(range(2, 13), 5)]
    grid = [Q(i, 16) for i in range(17, 257)]
    cores += [(1, *sorted(rng.sample(grid, 5))) for _ in range(500)]
    pinch_reach, ss_reach = Counter(), Counter()
    bad = []
    for core in cores:
        cells = clear_cells(core)
        for offset in (Q(1, 16), Q(1, 4), 1, 3, 8, 16):
            d = max(core) + offset
            wide = any(d * (b - a) >= 2 * R for a, b in cells)
            pair = (not wide) and any(incompatible(d, c, e)
                                      for c, e in combinations(cells, 2))
            label = ("one cell" if wide else
                     "pair" if pair else "common rejection")
            if pinch_fires(core, d, cells):
                pinch_reach[label] += 1
                if label == "common rejection":
                    bad.append(("pinch", core, d))
            if seam_scissors_fires(core, d, cells):
                ss_reach[label] += 1
                if label == "common rejection":
                    bad.append(("seam-scissors", core, d))
    emit("reach over the 5,772 controls, by verdict label:")
    emit(f"  pinch hypothesis fires: {dict(pinch_reach)}  (total {sum(pinch_reach.values())})")
    emit(f"  seam+scissors ratio-band hypothesis fires: {dict(ss_reach)} "
         f"(total {sum(ss_reach.values())})")
    emit(f"  unsound fires (on 'common rejection'): {len(bad)}")

    d0 = {}
    with open(os.path.join(N8, "j2_g1sweep_checkpoint.jsonl")) as f:
        for l in f:
            l = l.strip()
            if not l:
                continue
            try:
                rr = json.loads(l)
            except Exception:
                continue
            d0[tuple(rr["t"])] = rr
    allt = set(combinations_with_replacement(range(1, 18), 6))
    chain = sorted(t for t in allt if t in d0 and d0[t].get("s1") == "chain")
    cb_p, cb_s, cb_tot = 0, 0, 0
    for t in chain:
        core = (Q(1),) + tuple(Q(x) for x in t[:5])
        cells = clear_cells(core)
        for dd in (Q(t[5]),) + tuple(Q(t[5]) + off for off in
                                     (Q(1, 16), Q(1, 4), 1, 3, 8, 16)):
            cb_tot += 1
            wide = any(dd * (b - a) >= 2 * R for a, b in cells)
            if wide:
                continue
            if pinch_fires(core, dd, cells):
                cb_p += 1
            if seam_scissors_fires(core, dd, cells):
                cb_s += 1
    emit(f"chain-box probes (73 boxes x 7 rates = {cb_tot}): pinch fires {cb_p} "
         f"(non-wide probes only), seam+scissors fires {cb_s}")
    with open(os.path.join(HERE, "audit92_pinchreach.out"), "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
