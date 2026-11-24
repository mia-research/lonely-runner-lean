#!/usr/bin/env python3
"""Run m4_zone_cover_v1.run on every M4 box (6-tuples t of m4comp_cert_ckpt_v1.jsonl, n = 1::t),
pin 0.  Output one JSON line per box."""
import sys, json
sys.path.insert(0, '.')
from multiprocessing import Pool
from m4_zone_cover_v1 import run
if __name__ == "__main__":
    ts = [[1] + list(json.loads(l)["t"]) for l in open('m4comp_cert_ckpt_v1.jsonl')]
    order = sys.argv[1] if len(sys.argv) > 1 else None
    if order == 'hard':
        ts = [json.loads(l) for l in open(sys.argv[2])]
    with Pool(int(sys.argv[3]) if len(sys.argv) > 3 else 6) as p:
        for r in p.imap_unordered(run, ts, chunksize=4): print(json.dumps(r), flush=True)
