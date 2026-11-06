# E826: exact (Fractions) carve test of [1,7] by open zone intervals ((8j-1)/r, (8j+1)/r); a carve needs the open intervals to overlap strictly from 1 to 7.  Applied to the violators printed by frontier_carve_near_v1.out.
import re, math
from fractions import Fraction as F
def carves(rs):
    iv = []
    for r in rs:
        r = F(r)
        for j in range(1, int(7 * r / 8) + 3):
            a, b = F(8 * j - 1) / r, F(8 * j + 1) / r
            if b > 1 and a < 7: iv.append((a, b))
    iv.sort(); cur = F(1); first = True
    # point 1 itself must be covered: need an interval with a < 1 < b
    if not any(a < 1 < b for a, b in iv): return False, 'R=1 uncovered'
    reach = max(b for a, b in iv if a < 1)
    cur = reach; 
    while cur <= 7:
        nxt = [b for a, b in iv if a < cur and b > cur]
        if not nxt: return False, 'gap at R = %.9f' % float(cur)
        cur = max(nxt)
    return True, ''
lines = open('frontier_carve_near_v1.out').read().split('\n')
vs = []
for l in lines:
    if l.startswith('(np.float64'):
        vs.append([float(x) for x in re.findall(r'np\.float64\(([0-9.e+-]+)\)', l)])
import pickle
vs = pickle.load(open('frontier_carve_viol_v1.pkl', 'rb'))
nc = 0; bad = []
for v in vs:
    ok, why = carves(v)
    if ok: nc += 1; bad.append(v)
print('grid violators', len(vs), 'exact carves among them:', nc)
for v in bad[:5]: print('EXACT CARVE WITH SEAM VIOLATION', v, float(F(31) / F(v[4]) - F(73) / F(v[5])))
# positive control: the exact vector2
v2 = [F(3221761554497, 1099511627776), F(4334178521711, 1099511627776), F(2687190683461, 549755813888), F(7081933799491, 1099511627776), F(481036336437, 68719476736), F(18124207743665, 1099511627776)]
print('control vector2 exact carve:', carves(v2), '| seam 31/r6 - 73/r7 =', float(F(31) / v2[4] - F(73) / v2[5]))
