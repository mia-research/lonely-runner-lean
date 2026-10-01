"""E237 (2026-10-01): E1 restated after reading its three exceptions (hole_perturb_e1_read_v1.out).

E1': moving h alone to h* = (8K+1)/(8 b0) reaches the wall g = b0 iff every block reading other than h is clear at b0.
Derived: the move of h shifts no other reading.  If another block reading x is in the way at b0, then with h at h* the
block is not clear at b0, the relay's landing is at least x's exit past b0, and the move cannot bring g to b0 (region
moved).  If every other block reading is clear at b0, then at h* the block is clear at b0 = h*'s exit on lap K.
Checked on every overrun whose W_h move keeps the speed order (hole_perturb_v2's wall_check decides region moved).
"""
import sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
import hole_perturb_v2 as P, hole3_cascade_v1 as H3, holef_cascade_v1 as HF
from quantity_tests_v1 import cd, E8


def one(cb):
    core, block = cb
    st0 = P.state(core, block)
    if st0['h'] is None or st0['c'] is None:
        return None
    fr, rr, nn, wd = P.wall_check(core, block, st0, 'W_h')
    if any('skipped' in k for k in rr):
        return None
    moved = any(k.endswith('region moved') for k in rr)
    others_clear = all(cd(x * st0['b0']) >= E8 for x in block if x != st0['h'])
    return (others_clear, moved, core, block)


if __name__ == '__main__':
    pop = list(H3.gen(232, 2000)) + list(HF.gen(4, 238, 1000)[0])
    with Pool(8) as pool:
        rs = pool.map(HF.study, pop, chunksize=25)
        res = [x for x in pool.map(one, [(r['core'], r['block']) for r in rs if r['k_land'] != 'S0']) if x]
    out = open('hole_perturb_e1_refined_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    c = Counter((x[0], x[1]) for x in res)
    w("(every other block reading clear at b0, region moved): %s" % dict(c))
    w("E1' failures (clear and moved, or not clear and kept): %d of %d" % (c[(True, True)] + c[(False, False)], len(res)))
    for x in res:
        if x[0] == x[1]:
            w("  %s %s" % (x[2], x[3]))
    out.close()
    print(open('hole_perturb_e1_refined_v1.out').read()[len(__doc__):])
