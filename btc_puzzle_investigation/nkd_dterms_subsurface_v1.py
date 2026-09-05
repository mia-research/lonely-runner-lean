#!/usr/bin/env python3
"""
nkd_dterms_subsurface_v1.py -- does bounding reconstruction complexity (D_terms <= t)
punch HOLES into the (n,k,D) validity solid? EXACT integers + permutation control.

Full enumeration at bit-length N => every fiber (fixed (n,k)) is the COMPLETE contiguous
integer interval [Dmin,Dmax], with a term-count T(D)=d_terms defined at every D. The
sublevel set  A_t = { D in fiber : T(D) <= t }  can FRAGMENT the fiber into disconnected
runs. #components(A_t) - 1 = holes punched in that fiber by the complexity bound.

The topological question: is the fragmentation STRUCTURED (low-complexity D cluster or
avoid each other in an arithmetic way) or generic (same as a random arrangement of the
same term-count multiset)? Control = permute T-values within the fiber (keeps the multiset,
kills the arrangement). Real vs control #components => structured or not.

Exact integers; the permutation control is a count statistic (no float threshold on data).
"""
import sys, random
from collections import defaultdict
from exact_core import best_nk, residual, d_terms, lo_of


def components(present_sorted):
    """present_sorted: sorted list of integer positions present. #maximal contiguous runs."""
    if not present_sorted:
        return 0
    comp = 1
    for i in range(1, len(present_sorted)):
        if present_sorted[i] != present_sorted[i - 1] + 1:
            comp += 1
    return comp


def analyze_fiber(Tvals, tmax=4, ctrl_seeds=16):
    """Tvals: list of T(D) indexed by fiber position 0..width-1 (D ascending).
    Return per-t (real_components, mean_ctrl_components)."""
    width = len(Tvals)
    out = {}
    positions = list(range(width))
    for t in range(tmax + 1):
        present = [i for i in range(width) if Tvals[i] <= t]
        real_c = components(present)
        # permutation control: shuffle which position holds which T-value
        csum = 0
        for s in range(ctrl_seeds):
            rng = random.Random(1000 * s + 7)
            perm = Tvals[:]
            rng.shuffle(perm)
            pres = [i for i in range(width) if perm[i] <= t]
            csum += components(pres)
        out[t] = (real_c, csum / ctrl_seeds if ctrl_seeds else 0)  # noqa: float (report only)
    return out


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    top = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    lo = lo_of(N)
    print(f"# Full enumeration N={N}: {lo} keys (d in [2^{N-1}, 2^N)). Exact.")
    fibers = defaultdict(list)   # (n,k) -> list of (D, T)
    for d in range(lo, 2 * lo):
        n, k = best_nk(d, N, 256)
        D = residual(d, N, n, k)
        T = d_terms(d, N, n, k)
        fibers[(n, k)].append((D, T))
    widths = sorted(((max(D for D, _ in v) - min(D for D, _ in v) + 1, nk)
                     for nk, v in fibers.items()), reverse=True)
    print(f"# {len(fibers)} fibers. Widest {top} fibers (small n dominate width ~ lo/n^2):\n")
    print(f"# analyzing sublevel sets A_t = {{D: T(D)<=t}} — real #components vs "
          f"within-fiber permutation-control mean")
    print(f"{'(n,k)':>9} {'width':>8} | " + " ".join(f"t={t}:real/ctrl" for t in range(5)))
    agg_real = defaultdict(int); agg_ctrl = defaultdict(float); nfib = 0
    widest_profile = None
    for wi, (w, nk) in enumerate(widths[:top]):
        v = sorted(fibers[nk])           # by D ascending
        # verify contiguity (each D present once)
        Ds = [D for D, _ in v]
        contig = (Ds[-1] - Ds[0] + 1 == len(Ds)) and len(set(Ds)) == len(Ds)
        Tvals = [T for _, T in v]
        res = analyze_fiber(Tvals, tmax=4, ctrl_seeds=16)
        cells = " ".join(f"{res[t][0]:>4}/{res[t][1]:>6.1f}" for t in range(5))
        flag = "" if contig else "  <NONCONTIG!>"
        print(f"{str(nk):>9} {w:>8} | {cells}{flag}")
        for t in range(5):
            agg_real[t] += res[t][0]; agg_ctrl[t] += res[t][1]
        nfib += 1
        if wi == 0:
            widest_profile = (nk, Tvals)
    print(f"\n# AGGREGATE over widest {nfib} fibers: sum real #components vs sum control")
    for t in range(5):
        r, c = agg_real[t], agg_ctrl[t]
        ratio = (r / c) if c else 0.0  # noqa: float (report)
        print(f"   t={t}: real={r:>5}  ctrl={c:>8.1f}  real/ctrl={ratio:.3f}"
              f"   holes(real,=comp-1 summed)={r-nfib}")

    # dump the widest fiber's T-run structure to eyeball self-similarity
    nk, Tvals = widest_profile
    from collections import Counter
    print(f"\n# widest fiber {nk}: T-value histogram = {dict(sorted(Counter(Tvals).items()))}")
    # run-length view of {T<=1} across the fiber (compressed): lengths of present/absent runs
    runs = []; cur = (Tvals[0] <= 1); ln = 0
    for T in Tvals:
        p = (T <= 1)
        if p == cur: ln += 1
        else: runs.append((cur, ln)); cur, ln = p, 1
    runs.append((cur, ln))
    present_runs = [ln for pr, ln in runs if pr]
    absent_runs = [ln for pr, ln in runs if not pr]
    print(f"# {{T<=1}} present-run lengths (first 20): {present_runs[:20]}")
    print(f"# {{T<=1}} absent-run  lengths (first 20): {absent_runs[:20]}")
    print(f"# #components{{T<=1}}={len(present_runs)}  #holes={max(len(present_runs)-1,0)}")


if __name__ == "__main__":
    main()
