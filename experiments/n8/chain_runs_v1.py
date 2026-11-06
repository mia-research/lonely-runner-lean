# E645: exact chain length of the real-y certificate against the AP/grid run structure of the six.
import sys, time
from fractions import Fraction as F
from gen_real_core_v1 import cert
def runs(core):
    s = sorted(core); r = []; cur = [s[0]]
    for x in s[1:]:
        if x == cur[-1] + 1: cur.append(x)
        else: r.append(cur); cur = [x]
    r.append(cur); return [len(c) for c in r]
if __name__ == '__main__':
    cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt') if l.strip()]
    t0 = time.time()
    for c in cores[:5]:
        r = cert(c)
        print(c, 'chain', len(r['chain']) if r else None, 'runs', runs(c), 'y0', r['y0'] if r else None, round(time.time()-t0, 1))
