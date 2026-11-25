# E844 item 6: is the clear-free stretch of m positive speeds bounded (in units of 1/b1)?
# Step 1 (steer, floats): search integer speed sets n_1<...<n_m and phases phi with
#   max_t min_i ||n_i t + phi_i|| < 1/8   (shifted problem blocked at 1/8 over one period).
# Step 2 (exact): for each hit, round phi to rationals and verify exactly that the open arcs
#   {t : ||n_i t + phi_i|| < 1/8} cover [0,1).
import itertools, random, math
from fractions import Fraction as F
random.seed(844)
def clear_max(ns, ph, K=4000):
    best=0.0
    for k in range(K):
        t=k/K; v=min(abs(((n*t+p)%1+0.5)%1-0.5) for n,p in zip(ns,ph)); best=max(best,v)
    return best
def arcs(ns, ph):
    A=[]
    for n,p in zip(ns,ph):
        for j in range(n):  # n t + p in (j-1/8, j+1/8) mod 1 -> t in ((j-1/8-p)/n, (j+1/8-p)/n)
            a=(F(j)-F(1,8)-p)/n; b=(F(j)+F(1,8)-p)/n
            A.append((a%1, (a%1)+(b-a)))
    return A
def covers(A):
    # does the union of open arcs (a, a+L) on the circle [0,1) cover it? unroll to [0,2)
    iv=sorted(A+[(a+1,b+1) for a,b in A])
    # need a point x0 covered, then walk; open arcs: coverage needs strict overlap of ends
    for a0,b0 in iv[:len(A)]:
        reach=b0; start=a0; changed=True
        while changed:
            changed=False
            for a,b in iv:
                if a<reach and b>reach: reach=b; changed=True
        if reach>start+1: return True
    return False
hits=[]
for m in (4,5,6):
    for ns in itertools.combinations(range(1,13), m):
        if math.gcd(*ns)!=1: continue
        best=None
        for trial in range(40):
            ph=[0.0]+[random.random() for _ in range(m-1)]
            v=clear_max(ns,ph,1200)
            # local descent
            step=0.05
            for it in range(150):
                i=random.randrange(1,m); q=list(ph); q[i]=(q[i]+random.uniform(-step,step))%1
                w=clear_max(ns,q,1200)
                if w<v: ph,v=q,w
                else: step*=0.98
            if best is None or v<best[0]: best=(v,ph)
            if v<0.125-1e-3: break
        if best[0]<0.125-1e-3:
            phq=[F(round(p*4096),4096) for p in best[1]]
            ok=covers(arcs(ns,phq))
            hits.append((m,ns,ok,[str(p) for p in phq]))
            print('HIT', m, ns, 'float max clear', round(best[0],5), 'exact cover', ok, [str(p) for p in phq], flush=True)
            if ok and sum(1 for h in hits if h[0]==m and h[2])>=3: break
    print('m',m,'exact-verified blocked sets', sum(1 for h in hits if h[0]==m and h[2]), flush=True)
