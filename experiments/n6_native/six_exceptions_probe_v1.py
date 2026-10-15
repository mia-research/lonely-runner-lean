#!/usr/bin/env python3
"""Probe the rank-one (largest-flank) failures among primitive 5-sets in [1,80]
(six_largest_flank_v3_all80.out). For each: which SixResidual field fails (the rule that settles
it), gcd with 6 of each element, whether the second-largest flank carries a certificate, and the
certificate flanks. Exact integers."""
import importlib.util, math
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
def fields(S):
    M = sum(1 for d in S if d % 6 == 0); E = 5 - M
    return {'four': any(d % 4 == 0 for d in S), 'five': any(d % 5 == 0 for d in S),
            'spread': 5 * S[0] < S[-1],
            'shape': (M == 1 and E == 4) or (M == 2 and E == 3) or (M == 3 and all(d % 3 == 0 for d in S)),
            'no_free_flank': not any(r.free_flank(S, e) for e in S if e % 6 == 0),
            'not_fast': all(any(s != V and V <= 5 * s for s in S) for V in S)}
rows = [tuple(map(int, l.split()[1:6])) + (l.split()[6],) for l in open("six_largest_flank_v3_all80.out") if l.startswith("FAIL")]
settle = Counter(); second_ok = Counter()
print("RESIDUAL failures:")
for row in rows:
    S, tag = row[:5], row[5]
    f = fields(S); failed = [k for k, v in f.items() if not v]
    certs = r.certificates(S); bs = sorted({b for b, _ in certs})
    sec = S[3] in bs; second_ok[(tag, sec)] += 1
    if tag == "settled-by-rules":
        for k in failed: settle[k] += 1
    else:
        print(f"  {S}  gcd6={[math.gcd(d,6) for d in S]}  M={sum(d%6==0 for d in S)}  cert flanks={bs}  second-largest ok={sec}")
print("rule-settled failures, by failed field (a set may fail several):", dict(settle))
print("second-largest flank carries a certificate:", dict(second_ok))
