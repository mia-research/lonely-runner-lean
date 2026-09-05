#!/usr/bin/env python3
"""MEASURED cost of stage A (e2(1) exact integer vector, the spec's 'O(n^2) per prime')
and stage B (minimal polynomial in Z[Y] by the exact coset-product in Z[x]/Phi_n)."""
import sys,time,resource
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import compute_e2_poly
from audit_n1_vsign_v2_minpoly import analyse
print(f"{'p':>6} {'n':>6} {'d':>5} {'stageA_s':>10} {'stageB_s':>11} {'maxbits':>9} {'rss_MB':>8}")
for p in [int(x) for x in sys.argv[1].split(',')]:
    t0=time.time(); n,h1,h2,W=compute_e2_poly(p); tA=time.time()-t0
    d=(n-1)//6
    t0=time.time(); r=analyse(p); tB=time.time()-t0
    bits=max(abs(x).bit_length() for x in r['minpoly'])
    rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e6
    print(f"{p:>6} {n:>6} {d:>5} {tA:>10.2f} {tB:>11.2f} {bits:>9} {rss:>8.0f}", flush=True)
