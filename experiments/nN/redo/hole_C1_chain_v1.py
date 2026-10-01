"""E260 (2026-10-02): the twin chain on the open configurations (hole_C1_flanks_v1.out).  For every C1 member whose
fastest cluster flank is shadowed: follow the chain flank -> the walker that shadows it alone (if any) -> that walker's
own flank -> ..., recording each link's state (free / one walker (A, eps) / hand-off), until a free flank is reached or
the chain breaks.  The derived claim (E253) to check: the chain descends through near twins (A = 1, eps < 0) and ends at
a free flank."""
import sys, json
from fractions import Fraction as F
from collections import Counter
sys.path.insert(0, '../band_cert_v1')
from hole_C1_flanks_v1 import flank

M = json.load(open('../residual_members_C_list_v1.json'))
out = open('hole_C1_chain_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
ends = Counter()
for mode in 'AB':
    for S in M[mode]:
        S = tuple(sorted(S)); c = S[0]; cl = list(S[1:])
        e = cl[-1]; st = flank(c, cl, e)
        if st['state'] == 'free':
            continue
        chain = []
        while True:
            chain.append((cl.index(e) + 1, st['state'], st.get('walker')))
            if st['state'] != 'alone':
                break
            x = cl[st['walker'][0] - 1]
            e = x; st = flank(c, cl, e)
            if len(chain) > 6:
                break
        last = chain[-1][1]
        ends[(mode, 'ends at a free flank' if last == 'free' else 'ends ' + last, 'all links near twins (A=1, eps<0)' if all(l[2] is None or (l[2][1] == 1 and l[2][3] < 0) for l in chain) else 'other links')] += 1
        w("%s  %s" % (mode, ' -> '.join('rank %d %s%s' % (r, s, '' if wk is None else ' by rank %d (A=%d, eps=%.5f)' % (wk[0], wk[1], wk[3])) for r, s, wk in chain)))
w("chains: %s" % dict(ends))
out.close()
print(open('hole_C1_chain_v1.out').read()[len(__doc__):])
