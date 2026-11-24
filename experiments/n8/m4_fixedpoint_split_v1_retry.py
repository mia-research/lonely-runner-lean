#!/usr/bin/env python3
"""Retry the 217 budget-exhausted (box, pin) cases of m4_fixedpoint_split_v1.jsonl at budget 2,000,000."""
import json, sys
sys.path.insert(0, '.')
from multiprocessing import Pool
from m4_fixedpoint_split_v1 import split_box, face, ONE
def job(np):
    n, p = np
    faces = [face(v) for v in n]; faces[p] = (ONE, ONE)
    L, D, fail, nodes = split_box(faces, {p}, 2000000)
    return {"n": n, "pin": p, "leaves": L, "depth": D, "nodes": nodes,
            "fail": None if fail is None else [[str(a), str(b)] for a, b in fail]}
if __name__ == "__main__":
  cases = []
  for l in open('m4_fixedpoint_split_v1.jsonl'):
    r = json.loads(l)
    for c in r['cases']:
        if c['fail']: cases.append((r['n'], c['pin']))
  with Pool(10) as pool:
    for r in pool.imap_unordered(job, cases):
        print(json.dumps(r), flush=True)
