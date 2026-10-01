"""E237 (2026-10-01): the three overruns outside explanation E1 (hole_perturb_regions_v1.out), read move by move:
the block's relay from tau_C at the original h, and either side of the wall h* = (8K+1)/(8 b0)."""
import sys
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
import hole_perturb_v2 as P, hole3_cascade_v1 as H3, holef_cascade_v1 as HF

if __name__ == '__main__':
    pop = list(H3.gen(232, 2000)) + list(HF.gen(4, 238, 1000)[0])
    with Pool(8) as pool:
        rs = pool.map(HF.study, pop, chunksize=25)
    over = [(r['core'], r['block']) for r in rs if r['k_land'] != 'S0']
    out = open('hole_perturb_e1_read_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    for core, block in over:
        st0 = P.state(core, block)
        g, gm = P.relay(block, st0['tc'])
        if [mv[3] for mv in gm if mv[3] > st0['b0']] != [g]:
            continue
        fr, rr, nn, wd = P.wall_check(core, block, st0, 'W_h')
        if not any(k.endswith('region moved') for k in rr):
            continue
        h, K, b0 = st0['h'], st0['K'], st0['b0']; hw = F(8 * K + 1) / (8 * b0)
        w("\ncore %s block %s  h %s K %s  h*/h %.5f" % (core, block, h, K, float(hw / h)))
        for lab, v in (('original', h), ('outside', hw * (1 - P.ETA)), ('inside', hw * (1 + P.ETA))):
            X = P.state(*P.swap(core, block, h, v)) if v != h else st0
            g2, gm2 = P.relay(X['block'], X['tc'])
            w("  %-8s tc %.9f b0 %.9f g %.9f landing stretch %s (h,K)=(%s,%s)" % (lab, float(X['tc']), float(X['b0']), float(X['g']), X['kl'],
                                                                             round(float(X['h']), 3) if X['h'] else None, X['K']))
            for t, way, st, nx in gm2:
                w("      from %.9f way %s setter %s -> %.9f" % (float(t), [round(float(d), 3) for d in way], [round(float(d), 3) for d in st], float(nx)))
    out.close()
    print(open('hole_perturb_e1_read_v1.out').read())
