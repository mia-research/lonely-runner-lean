#!/usr/bin/env python3
"""m4_zone_cert_all_v1 -- zone certificates (w = 0) for every sorted 7-tuple 1::v::w::x::t,
t in gen 3 x (the order of Fresh.M4SplitAssembly.gen), every one mirror-checked
(m4_zone_cert_v1.zc).  The 73 chain boxes get the placeholder leaf [] (the Lean verdict takes
isChainL first).  Output: m4_zone_certs_v1.jsonl, one line per tuple {l, chain, nodes, tree},
and a summary on stderr (tuples, chain, uncovered, total nodes, largest)."""
import sys, json
sys.path.insert(0, '.')
from multiprocessing import Pool
import m4_zone_cert_v1 as C

def gen(k, lo):
    if k == 0: return [[]]
    return [[v] + t for v in range(lo, 18) for t in gen(k - 1, v)]

CHAIN = {tuple(json.loads(l)['n']) for l in open('m4_chain_split_v1.jsonl')}

def job(l):
    if tuple(l) in CHAIN: return {"l": l, "chain": True, "nodes": 1, "tree": ["L", []]}
    t, st = C.cert(l, 0)
    if t is None: return {"l": l, "chain": False, "uncovered": st["uncovered"][:1]}
    return {"l": l, "chain": False, "nodes": C.size(t), "tree": t}

if __name__ == "__main__":
    ls = []
    for v in range(1, 18):
        for w in range(v, 18):
            for x in range(w, 18):
                for t in gen(3, x): ls.append([1, v, w, x] + t)
    print(len(ls), "tuples", file=sys.stderr, flush=True)
    tot = unc = ch = 0; big = (0, None)
    with Pool(8) as p, open('m4_zone_certs_v1.jsonl', 'w') as f:
        for i, r in enumerate(p.imap(job, ls, chunksize=16)):
            f.write(json.dumps(r) + "\n")
            if r.get("chain"): ch += 1
            if "uncovered" in r: unc += 1; print("UNCOVERED", r["l"], file=sys.stderr, flush=True)
            else:
                tot += r["nodes"]; big = max(big, (r["nodes"], r["l"]))
            if i % 5000 == 0: print(i, tot, big, file=sys.stderr, flush=True)
    print(json.dumps({"tuples": len(ls), "chain": ch, "uncovered": unc, "nodes": tot, "largest": big}), file=sys.stderr)
