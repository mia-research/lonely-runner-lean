#!/usr/bin/env sage
# AUDIT re-check: did I explain away a real secp difference at |V|=4?
# The [B2] CONSISTENT |V|=4 run showed secp quo=12/d_gb=4 vs 6/3 for the controls. I dismissed it
# as an "uncontrolled per-curve target artifact" (consistent systems can't be matched across curves
# because the decomposable target depends on the curve's points). This re-check tests that dismissal
# the ONLY way it can be tested: the matched INCONSISTENT control (identical V + target across all
# three curves, so the sole difference is (A,B) in the lower-order terms), extended to larger |V|=B.
# If secp = non-CM = j1728 at matched |V|=4,5 -> the [B2] difference was indeed the target, not CM.
# If secp DIVERGES here -> I wrongly dismissed a real curve effect and E must be reopened.
from sage.all import *
load("semaev_elimination_v1.py")

def main():
    import sys; sys.stdout.reconfigure(line_buffering=True)
    print("AUDIT: matched INCONSISTENT control at larger |V| (identical V,t across curves)")
    for p, m, B in [(211, 3, 3), (211, 3, 4), (307, 3, 4), (211, 3, 5)]:
        Dmax = 2**(m - 1) + m * B + 5
        comp = matched_curves_compare(p, m, B, seed=12345, Dmax=Dmax)
        print("  p=%d m=%d |V|=B=%d  t=%d" % (p, m, B, comp['tval']))
        degs = []
        for name, r in comp['res']:
            print("     %-18s dim=%s quo=%s d_ff=%s d_solv=%s d_gb=%s"
                  % (name, r['dim'], r['quo'], r['d_ff'], r['d_solv'], r['d_gb']))
            degs.append((r['d_ff'], r['d_solv'], r['d_gb']))
        same = all(d == degs[0] for d in degs)
        print("     -> secp == controls (d_ff,d_solv,d_gb)? %s" % same)

if __name__ == '__main__':
    main()
