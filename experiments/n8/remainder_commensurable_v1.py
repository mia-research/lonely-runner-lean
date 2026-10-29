# The survey arrangements left after the proved types and the fixed-instant list (E637): are they covered by the commensurable classes (no-multiple, one-free), and which flank lap (n + 1/8)/e lands them?  Exact.
import collections
from fractions import Fraction as F
exec(open('remainder_after_types_v1.py').read().split("rem = []; cnt = collections.Counter()")[0])
rem = []
for rec in S:
    r = sorted(rec[1])
    if unblocked(r) or ratio(r) or firstlap(r) or chain2(r) or fixedR(r): continue
    rem.append((rec[2], r))
c = collections.Counter()
for lab, r in rem:
    nm = nomultiple(r); of = onefree(r)
    c['nomult' if nm else ('onefree' if of else 'neither')] += 1
print(len(rem), dict(c))
def casc2(r):
    t = F(1, 8 * min(r)); last = None
    while True:
        way = [d for d in r if dist(d * t) < E]
        if not way: return t, last
        best = max(((F(round(d * t)) + E) / d, d) for d in way); t, last = best
js = collections.Counter(); es = collections.Counter()
for lab, r in rem:
    t, last = casc2(r)
    js[int(round(t * last - E))] += 1; es[r.index(last) if last else -1] += 1
print('opener lap n in remainder', dict(sorted(js.items())))
print('opener rank in remainder', dict(sorted(es.items())))
