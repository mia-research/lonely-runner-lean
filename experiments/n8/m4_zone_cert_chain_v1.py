#!/usr/bin/env python3
"""Zone certificates with w = 1 (R in [1,7] or [9,15]) for the 73 chain boxes, in the order of
Fresh.FilterAssemblyPerBox.chainBoxes (= m4_chain_split_v1.jsonl order is NOT assumed: the
order is read from the Lean source).  Mirror-checked.  Output m4_zone_certs_chain_v1.jsonl."""
import sys, json, re
sys.path.insert(0, '.')
from multiprocessing import Pool
import m4_zone_cert_v1 as C
src = open('../../LonelyRunnerFresh/Fresh/FilterAssemblyPerBox.lean').read()
body = src[src.index('def chainBoxes'):]; body = body[body.index('[') + 1:]
body = body[:body.index(']]') + 1]
ts = [[int(x) for x in m.split(',')] for m in re.findall(r'\[([0-9, ]+)\]', body)]
def job(t):
    l = [1] + t; tr, st = C.cert(l, 1)
    return {"t": t, "nodes": None if tr is None else C.size(tr), "tree": tr}
if __name__ == "__main__":
    print(len(ts), file=sys.stderr)
    with Pool(4) as p, open('m4_zone_certs_chain_v1.jsonl', 'w') as f:
        for r in p.imap(job, ts): f.write(json.dumps(r) + "\n")
