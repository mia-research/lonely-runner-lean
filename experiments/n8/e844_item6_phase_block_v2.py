# E844 item 6 probe, v2 (numpy steer + exact check).
# Question: for integer speeds n_1<...<n_m (gcd 1) is there a phase vector phi with
#   {t in [0,1): ||n_i t + phi_i|| >= 1/8 for all i} empty?  (blocked at 1/8)
# If yes, speeds near the n_i with independent perturbations give clear-free stretches of
# unbounded length in units of 1/b_1 (argument stated in the log entry, not checked here).
# Floats steer only; every reported hit is re-checked exactly with rational phases.
import itertools, math, numpy as np
from fractions import Fraction as F
rng=np.random.default_rng(844)
K=2048; T=(np.arange(K)+0.5)/K
def dist(x): return np.abs((x+0.5)%1-0.5)
def exact_blocked(ns, ph):
    # clear set of speed n with phase p: union over j of closed [ (j+1/8-p)/n , (j+7/8-p)/n ] mod 1
    # blocked iff the intersection over i of these closed sets is empty; check all candidate
    # endpoints and midpoints of the common refinement.
    pts=set()
    for n,p in zip(ns,ph):
        for j in range(n):
            for e in (F(1,8),F(7,8)): pts.add(((j+e-p)/n)%1)
    pts=sorted(pts); cand=list(pts)+[(pts[k]+pts[k+1])/2 for k in range(len(pts)-1)]+[((pts[-1]+pts[0]+1)/2)%1]
    def d(x): x=x%1; return min(x,1-x)
    for t in cand:
        if all(d(n*t+p)>=F(1,8) for n,p in zip(ns,ph)): return False, t
    return True, None
out=[]
for m in (5,6):
    found=0; tested=0
    for ns in itertools.combinations(range(1,11), m):
        if math.gcd(*ns)!=1: continue
        tested+=1
        N=np.array(ns)[:,None]
        P=rng.random((4000,m)); P[:,0]=0
        best=None
        for chunk in range(0,4000,500):
            ph=P[chunk:chunk+500]
            v=dist(N[None,:,:]*T[None,None,:]+ph[:,:,None]).min(axis=1).max(axis=1)
            k=int(v.argmin())
            if best is None or v[k]<best[0]: best=(float(v[k]),ph[k].copy())
        v,ph=best; step=0.03
        for it in range(400):
            q=ph.copy(); i=rng.integers(1,m); q[i]=(q[i]+rng.uniform(-step,step))%1
            w=float(dist(N*T[None,:]+q[:,None]).min(axis=0).max())
            if w<v: v,ph=w,q
            else: step=max(step*0.99,1e-4)
        if v<0.125-1e-4:
            phq=[F(round(float(p)*8192),8192) for p in ph]
            ok,_=exact_blocked(ns,phq)
            print('HIT m=%d'%m, ns, 'steer max-clear %.5f'%v, 'exact blocked', ok, [str(p) for p in phq], flush=True)
            if ok: found+=1
            if found>=5: break
    print('m=%d tested %d speed sets, exact-blocked found %d (search stops at 5)'%(m,tested,found), flush=True)
