# v3_growth_profile_v2 -- instrumented copy of chain_cover_v4.search (same logic, exact Fractions) for the V3 box
# 1<=rho2<=..<=rho7<=B, rho6>17, rho7>=25.  Counts nodes by depth (chain length), children tried/kept, and the
# reason each candidate (reading y, lap j) was rejected: ENTRY (entry<=exit fails), PROGRESS, IRRED.
import sys, time, json
from fractions import Fraction as F
sys.path.insert(0, '.')
from d0_points_only_k6_v2 import base_system

def profile(B, rho6lo, rho7lo, deadline, nread=7, h=F(1), windows=[(F(1),F(7))]):
    B = F(B)
    s0 = base_system(nread, B)
    assert s0.add(nread-2, 0, 1/F(rho6lo), True)
    assert s0.add(nread-1, 0, 1/F(rho7lo), False)
    stack = [(s0, 0, None, None, [])]
    nodes = 0; bydepth = {}; kept = {}; rej = {'ENTRY':0,'PROGRESS':0,'IRRED':0}; fin = 0; covers = 0
    ky = {}; kj = {}
    while stack:
        if time.time() > deadline: return dict(ky=ky, kjn={y:len(v) for y,v in kj.items()}, B=str(B), status='CAP', nodes=nodes, bydepth=bydepth, kept=kept, rej=rej, fin=fin, covers=covers)
        s, wi, cur, prev, chain = stack.pop()
        nodes += 1; d = len(chain); bydepth[d] = bydepth.get(d,0)+1
        lo, hi = windows[wi]
        ce, cv = (lo, 0) if cur is None else (8*cur[1]+h, cur[0])
        M = s.M
        xmin = ce / M[0][cv][0]; xmax = ce * M[cv][0][0]
        jmax = int((hi*B + h)//8) + 1
        for y in range(1, nread):
            uymin = 1 / M[0][y][0]; uymax = M[y][0][0]
            jlo = max(1, int((xmin/uymax - h)//8)); jhi = min(jmax, int((xmax/uymin + h)//8) + 1)
            for j in range(jlo, jhi+1):
                if (wi,y,j) in chain: continue
                t = s.copy()
                if not t.add(y, cv, F(ce)/(8*j-h), True): rej['ENTRY']+=1; continue
                if not t.add(cv, y, (8*j+h)/F(ce), True): rej['PROGRESS']+=1; continue
                if prev is not None:
                    pe, pv = prev
                    if not t.add(pv, y, (8*j-h)/F(pe), True): rej['IRRED']+=1; continue
                kept[d] = kept.get(d,0)+1; ky[y] = ky.get(y,0)+1; kj.setdefault(y,set()).add(j)
                tf = t.copy()
                if tf.add(0, y, (8*j+h)/F(hi), True):
                    covers += 1; fin += 1; continue
                stack.append((t, wi, (y,j), (ce,cv), chain+[(wi,y,j)]))
    return dict(ky=ky, kjn={y:len(v) for y,v in kj.items()}, B=str(B), status='DONE', nodes=nodes, bydepth=bydepth, kept=kept, rej=rej, fin=fin, covers=covers)

if __name__ == "__main__":
    B = sys.argv[1]; secs = int(sys.argv[2])
    t = time.time()
    r = profile(B, 17, 25, time.time()+secs)
    r['secs'] = round(time.time()-t,1)
    print(json.dumps(r))
