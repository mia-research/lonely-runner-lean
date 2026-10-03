# sigpair_nice_v1 -- readable exact witnesses: round each exact witness to denominator 10^k (smallest k that keeps the exact (opener, closer) pair), verify with outcome()
import pickle, json, glob, sys
from fractions import Fraction as F
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
W = pickle.load(open('sigpair_witnesses_nodes_v1.pkl', 'rb'))
out = {}
for k, v in sorted(W.items()):
    best = None
    for isterm, L, rho in v:
        rho = [F(x) for x in rho]
        for d in (10**2, 10**3, 10**4, 10**5, 10**6):
            r2 = [F(1)] + [F(round(x * d), d) for x in rho[1:]]
            if len(set(r2)) < 7 or r2 != sorted(r2) or r2[6] > 17: continue
            o = outcome(r2)
            if o['opener'] and (o['opener'][0], o['closer'][0]) == k:
                if best is None or d < best[0]: best = (d, r2, o)
                break
    if best:
        d, r2, o = best
        print(k, 'denominator 10^%d' % len(str(d)[1:]), [str(x) for x in r2], 'R*=%s' % o['R'], 'opener', o['opener'], 'closer', o['closer'], 'width', float(o['width']), 'moves', len(o['path']))
        out[str(k)] = [str(x) for x in r2]
json.dump(out, open('sigpair_nice_witnesses_v1.json', 'w'))
