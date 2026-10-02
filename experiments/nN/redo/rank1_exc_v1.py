"""E264: the members whose slowest cluster flank (rank 1) is not free across c's run (free_ranks_v1.py): per member, the shadow
at rank 1 (one walker: its rank, A mod 8, eps; or hand-off occupants), the ratios x/c, residues mod 8, and which flanks are free."""
import sys, os, json
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
import restricted_b_v1 as R, free_ranks_v1 as FR
from hole_C1_flanks_v1 import flank
from multiprocessing import Pool
def go(item):
    seed, mode, S = item; c = S[0]; cl = list(S[1:])
    r = flank(c, cl, cl[0])
    if r['state'] == 'free': return None
    st = [flank(c, cl, e)['state'] for e in cl]
    return seed, mode, S, r, st
if __name__ == '__main__':
    M = json.load(open(R.NN + '/residual_members_C_list_v1.json'))
    items = [(118, m, tuple(S)) for m in 'AB' for S in M[m]]
    with Pool(10) as pool:
        for part in pool.map(FR.members, range(201, 211)): items += part
        res = [r for r in pool.map(go, items, chunksize=40) if r]
    out = open('rank1_exc_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    w("rank-1 flank not free: %d members" % len(res))
    for seed, mode, S, r, st in res:
        c = S[0]; cl = S[1:]
        d = {k: (v if k != 'occ' else [(o[0], o[1], o[2], o[3], round(o[4], 3)) for o in v]) for k, v in r.items() if k in ('state', 'n', 's', 'walker', 'occ')}
        w("seed %d %s: x/c %s; mod8 %s; rank1 %s; states %s" % (seed, mode, [round(x / c, 2) for x in cl], [x % 8 for x in S], d, st))
    out.close(); print(open('rank1_exc_v1.out').read()[len(__doc__):])
