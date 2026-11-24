#!/usr/bin/env python3
"""Retry3: pin-0 hard cases with a DEPTH cap of 80 (no terminating case has exceeded depth 48)
and a node budget of 5,000,000.  A case hitting the depth cap is recorded as STALL with the
deepest box.  Finished results of retry and retry2 are reused."""
import json, sys
sys.path.insert(0, '.')
from multiprocessing import Pool
from m4_fixedpoint_split_v1 import feasible, face, ONE

def job(n, budget=5000000, dcap=80):
    faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
    st = [(faces, 0)]; L = D = N = 0
    while st:
        fc, d = st.pop(); N += 1
        if N > budget: return {"n": n, "status": "BUDGET", "nodes": N, "leaves": L}
        if feasible(fc) is not None: L += 1; D = max(D, d); continue
        if d >= dcap:
            return {"n": n, "status": "STALL", "nodes": N, "leaves": L, "box": [[str(a), str(b)] for a, b in fc]}
        k = max(range(1, 7), key=lambda i: (fc[i][1] - fc[i][0], -i))
        lo, hi = fc[k]; m = (lo + hi) / 2
        a = list(fc); a[k] = (lo, m); b = list(fc); b[k] = (m, hi); st += [(a, d + 1), (b, d + 1)]
    return {"n": n, "status": "OK", "leaves": L, "depth": D, "nodes": N}

if __name__ == "__main__":
    done = {}
    for f in ('m4_fixedpoint_split_v1_retry.jsonl', 'm4_fixedpoint_split_v1_retry2.jsonl'):
        for l in open(f):
            try: r = json.loads(l)
            except Exception: continue
            if r.get('pin') == 0 and r.get('fail') is None:
                done[tuple(r['n'])] = {"n": r['n'], "status": "OK", "leaves": r['leaves'], "depth": r['depth'], "nodes": r['nodes'], "reused": True}
    todo = []
    for l in open('m4_fixedpoint_split_v1.jsonl'):
        r = json.loads(l)
        for c in r['cases']:
            if c['pin'] == 0 and c['fail'] and tuple(r['n']) not in done: todo.append(r['n'])
    for r in done.values(): print(json.dumps(r), flush=True)
    print(json.dumps({"todo": len(todo), "reused": len(done)}), file=sys.stderr, flush=True)
    with Pool(8) as pool:
        for r in pool.imap_unordered(job, todo):
            print(json.dumps(r), flush=True)
