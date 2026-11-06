# E826: positive control and local search around the exact joint-lift witness vector2 of T2c (floats steer only): is vector2[1:] a carve of [1,7]; do perturbations that still carve ever violate 31/r6 <= 73/r7?
import numpy as np, sys
from fractions import Fraction as F
v2 = [F(1), F(3221761554497, 1099511627776), F(4334178521711, 1099511627776), F(2687190683461, 549755813888), F(7081933799491, 1099511627776), F(481036336437, 68719476736), F(18124207743665, 1099511627776)]
rs0 = np.array([float(x) for x in v2[1:]])
print('readings', rs0, 'r7', rs0[-1], '511/31', 511 / 31, 'seam 31/r6 <= 73/r7:', 31 / rs0[4] <= 73 / rs0[5])
fine = np.linspace(1, 7, 24001)[None, :]
coarse = np.linspace(1, 7, 700)[None, :]
def covered(rs, R):
    x = rs[:, :, None] * R[None, :, :]
    return (np.abs(x / 8 - np.round(x / 8)) < 1 / 8).any(axis=1)
print('positive control: vector2[1:] carves [1,7] on a 24001-point grid:', bool(covered(rs0[None, :], fine).all()))
rng = np.random.default_rng(int(sys.argv[1])); tot = carved = 0; viol = []
for scale in [1e-1, 3e-2, 1e-2, 3e-3, 1e-3]:
    for _ in range(int(sys.argv[2])):
        n = 2500
        rs = rs0[None, :] * (1 + scale * rng.uniform(-1, 1, (n, 6)))
        rs = np.sort(rs, axis=1)
        ok = (rs[:, 4] > 47 / 7) & (rs[:, 4] < 7) & (rs[:, 5] > 15) & (rs[:, 0] >= 1)
        rs = rs[ok]; tot += len(rs)
        if not len(rs): continue
        c0 = covered(rs, coarse).all(axis=1)
        rs = rs[c0]
        if not len(rs): continue
        c = covered(rs, fine).all(axis=1)
        for r in rs[c]:
            carved += 1
            if 31 / r[4] > 73 / r[5] + 1e-12: viol.append(tuple(r))
    print('scale', scale, 'cumulative samples', tot, 'carves', carved, 'seam violations', len(viol))
import pickle; pickle.dump([tuple(float(x) for x in v) for v in viol], open('frontier_carve_viol_v1.pkl', 'wb'))
for v in viol[:5]: print(v)
