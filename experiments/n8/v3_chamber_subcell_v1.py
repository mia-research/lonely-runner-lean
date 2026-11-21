# v3_chamber_subcell_v1 -- the gamma-resolution instrument (E915's named decision, priced):
# does the two-line race test (D1/D2) fire at SUB-CHAMBER resolution?
# Method: per chamber class (from the probe dump), the boundary readings' windows are
# rhoL in [(8kL-1)/a, (8kL+1)/a] ∩ cellL and rhoR in [(8kR-1)/b, (8kR+1)/b] ∩ cellR
# (chamber_test's own stability windows -- the same zone-edge assignment holds throughout).
# Subdivide K x K; at each sub-window compute q_min = rhoL_lo/rhoR_hi (the binding corner)
# and test D1: q_min >= 9*phi/7; D2: (8*J(q_min)+1)*rhoR_hi <= 25*(8kR-1).
# A sub-window that fires D1-or-D2 certifies column death for every tuple in it.
# The answer prices path (a): the fraction of the chamber's area the two-line covers,
# and the remainder's shape (which needs the intersection form or deeper subdivision).
from fractions import Fraction as F
import json, sys, itertools

CELLBOUNDS = {'P': (F(1),F(7)), 'S1': (F(7),F(9)), 'G1': (F(9),F(15)), 'S2': (F(15),F(17)), 'E': (F(17),F(17))}
def cell_of(x):
    if x <= F(7): return 'P'
    if x < F(9): return 'S1'
    if x <= F(15): return 'G1'
    if x < F(17): return 'S2'
    return 'E'

def phi_of(kL, kR): return F(8*kL+1, 8*kR-1)

def J_of(q, kL, kR):
    phi = F(8*kL+1, 8*kR-1)
    if q <= phi: return None
    j = 1; J = 0
    while F(8*j-1)*q < F(8*j+1)*phi:
        J = j; j += 1
        if j > 30000: return cap
    return J

def sub_windows(rlo, rhi, K):
    step = (rhi - rlo) / K
    return [(rlo + i*step, rlo + (i+1)*step) for i in range(K)]

def fires(wL, wR, kL, kR, rlo=F(25)):
    """D1 or D2 at this sub-window's binding corner (q_min = rhoL_lo/rhoR_hi)."""
    rhoL_lo, rhoL_hi = wL; rhoR_lo, rhoR_hi = wR
    if rhoL_lo > rhoL_hi or rhoR_lo > rhoR_hi: return 'degenerate'
    q_min = rhoL_lo / rhoR_hi
    phi = phi_of(kL, kR)
    thr = 9*phi/7
    if q_min >= thr: return 'D1'
    Jm = J_of(q_min, kL, kR)
    if Jm is None: return 'qle-phi'
    if F(8*Jm+1)*rhoR_hi <= rlo*F(8*kR-1): return 'D2'
    return 'OPEN'

def main(dump_path, out_path, K, max_chambers, deadline):
    t0 = __import__('time').time()
    classes = {}
    seen = 0
    for line in open(dump_path):
        d = json.loads(line)
        if d.get('type') != 'open': continue
        seen += 1
        c = d['case']
        key = (tuple(c['skel']), c['L'][1], c['R'][1], cell_of(F(c['L'][0])), cell_of(F(c['R'][0])), c['a'], c['b'])
        classes.setdefault(key, 0)
        classes[key] += 1
    print(f'dump: {seen} open cases, {len(classes)} classes (re-dedup)')
    a, b = F, F
    results = []
    n_done = 0
    for n, (key, cnt) in enumerate(sorted(classes.items(), key=lambda z: -z[1])):
        if n_done >= max_chambers or __import__('time').time() > deadline: break
        skel, kL, kR, cL, cR, astr, bstr = key
        astr2 = astr.split('/')[-1] if '/' in astr else astr  # not used; a,b are fractions like "35/27"
        a = F(astr); b = F(bstr)
        cL_lo, cL_hi = CELLBOUNDS[cL]; cR_lo, cR_hi = CELLBOUNDS[cR]
        # chamber_test's stability windows
        rhoL_lo = max(cL_lo, F(8*kL-1)/a); rhoL_hi = min(cL_hi, F(8*kL+1)/a)
        rhoR_lo = max(cR_lo, F(8*kR-1)/b); rhoR_hi = min(cR_hi, F(8*kR+1)/b)
        if rhoL_lo > rhoL_hi or rhoR_lo > rhoR_hi: continue
        wLs = sub_windows(rhoL_lo, rhoL_hi, K)
        wRs = sub_windows(rhoR_lo, rhoR_hi, K)
        fire = 0; tot = 0; kinds = {}
        for wL in wLs:
            for wR in wRs:
                v = fires(wL, wR, kL, kR)
                tot += 1
                if v in ('D1','D2'): fire += 1
                kinds[v] = kinds.get(v,0)+1
        results.append(dict(skel=list(skel), kL=kL, kR=kR, cL=cL, cR=cR, a=astr, b=bstr,
                            cases=cnt, fire=fire, tot=tot, frac=str(F(fire,tot)), kinds=kinds))
        n_done += 1
    fire_tot = sum(r['fire'] for r in results); area_tot = sum(r['tot'] for r in results)
    full = sum(1 for r in results if r['fire'] == r['tot'])
    zero = sum(1 for r in results if r['fire'] == 0)
    out = dict(K=K, chambers_probed=n_done, subwindows_total=area_tot,
               subwindows_firing=fire_tot, chambers_full_fire=full, chambers_zero_fire=zero,
               results=results)
    json.dump(out, open(out_path, 'w'), indent=1)
    print(f'chambers probed: {n_done} | sub-windows firing: {fire_tot}/{area_tot} | full-fire chambers: {full} | zero-fire: {zero}')
    print(f'-> {out_path}')

if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    maxch = int(sys.argv[2]) if len(sys.argv) > 2 else 150
    secs = int(sys.argv[3]) if len(sys.argv) > 3 else 2400
    main('/Users/trentpalelei/Desktop/Math Ex/experiments/n8/v3_chamber_open_v2_sweep.jsonl',
         '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/v3_chamber_subcell_v1.out',
         K, maxch, __import__('time').time() + secs)
