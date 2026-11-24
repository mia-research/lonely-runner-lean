#!/usr/bin/env python3
"""m4_budget_stallcell_v1 -- the 14 BUDGET boxes of retry3 (5,000,000 nodes, no depth-80 cell)
rerun with the same fixed-instant DFS (m4_fixedpoint_split_v1_retry3.job) at depth cap 60 and
budget 3,000,000, to capture a cell where the checker descends without a leaf.  Output in the
retry3 format (status STALL carries the cell)."""
import sys, json
sys.path.insert(0, '.')
from multiprocessing import Pool
from m4_fixedpoint_split_v1_retry3 import job
def j(n): return job(n, budget=3000000, dcap=60)
if __name__ == "__main__":
    ns = [r['n'] for r in map(json.loads, open('m4_fixedpoint_split_v1_retry3.jsonl')) if r.get('status') == 'BUDGET']
    with Pool(3) as p:
        for r in p.imap_unordered(j, ns): print(json.dumps(r), flush=True)
