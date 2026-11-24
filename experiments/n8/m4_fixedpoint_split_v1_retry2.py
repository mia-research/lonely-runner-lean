#!/usr/bin/env python3
"""Retry, pin 0 only (checkT checks only the pin at coordinate 0), the (box, pin 0) cases of
m4_fixedpoint_split_v1.jsonl that exhausted the 4,000-node budget, at budget 5,000,000.
Cases already finished in m4_fixedpoint_split_v1_retry.jsonl (parseable lines) are reused."""
import json, sys
sys.path.insert(0, '.')
from multiprocessing import Pool
from m4_fixedpoint_split_v1 import split_box, face, ONE

def job(n):
    faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
    L, D, fail, nodes = split_box(faces, {0}, 5000000)
    return {"n": n, "pin": 0, "leaves": L, "depth": D, "nodes": nodes,
            "fail": None if fail is None else [[str(a), str(b)] for a, b in fail]}

if __name__ == "__main__":
    done = {}
    for l in open('m4_fixedpoint_split_v1_retry.jsonl'):
        try: r = json.loads(l)
        except Exception: continue
        if r['pin'] == 0 and r['fail'] is None: done[tuple(r['n'])] = r
    todo = []
    for l in open('m4_fixedpoint_split_v1.jsonl'):
        r = json.loads(l)
        for c in r['cases']:
            if c['pin'] == 0 and c['fail'] and tuple(r['n']) not in done: todo.append(r['n'])
    for r in done.values(): print(json.dumps(dict(r, reused=True)), flush=True)
    print(json.dumps({"todo": len(todo), "reused": len(done)}), file=sys.stderr, flush=True)
    with Pool(8) as pool:
        for r in pool.imap_unordered(job, todo):
            print(json.dumps(r), flush=True)
