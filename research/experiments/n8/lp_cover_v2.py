"""v1 enumerated blindly and found nothing at length <= 4 (too short: intervals have width 2u <= 2
and the region is 6 units).  Blind enumeration is 24^len.  Here the LP prunes every PARTIAL chain:
extend only if "first interval contains a AND the chain links AND ordering holds" is still feasible.

Variables u_i = 1/s_i for i = 2..7 (indices 0..5), with
    1 > u_0 > u_1 > ... > u_5,   u_5 < 1/7   (S > 7, else clear at R = 1)
Bad interval (i,k) is [ (8k-1)u_i , (8k+1)u_i ].  Covering [a,b] needs a chain."""
import sys; sys.path.insert(0,'experiments/n8')
import numpy as np
from scipy.optimize import linprog
NC=6; EPS=1e-7
def build(chain, a, b=None):
    A=[]; rhs=[]
    def row(): return [0.0]*NC
    i0,k0=chain[0]
    r=row(); r[i0]=(8*k0-1); A.append(r); rhs.append(a)
    r=row(); r[i0]=-(8*k0+1); A.append(r); rhs.append(-a)
    for (ip,kp),(i,k) in zip(chain,chain[1:]):
        r=row(); r[i]+= (8*k-1); r[ip]-= (8*kp+1); A.append(r); rhs.append(-EPS)
    if b is not None:
        il,kl=chain[-1]
        r=row(); r[il]=-(8*kl+1); A.append(r); rhs.append(-b)
    for j in range(NC-1):
        r=row(); r[j]=-1.0; r[j+1]=1.0; A.append(r); rhs.append(-EPS)
    bounds=[(1/8+EPS,1-EPS)]*NC
    bounds[NC-1]=(1/8+EPS,1/7-EPS)
    return np.array(A), np.array(rhs), bounds
def feas(chain,a,b=None,maximise_reach=False):
    A,rhs,bnds=build(chain,a,b)
    c=[0.0]*NC
    if maximise_reach:
        il,kl=chain[-1]; c[il]=-(8*kl+1)          # maximise (8k+1)u_last
    r=linprog(c=c,A_ub=A,b_ub=rhs,bounds=bnds,method="highs")
    return (r.status==0), (r.x if r.status==0 else None)
def search(a,b,KMAX,MAXLEN,report=0):
    best=[0.0,None]; found=[]
    nodes=[0]
    def rec(chain):
        nodes[0]+=1
        if nodes[0]>400000: return
        ok,_=feas(chain,a)
        if not ok: return
        ok2,u=feas(chain,a,b)
        if ok2: found.append((list(chain),u)); return
        okr,ur=feas(chain,a,maximise_reach=True)
        if okr:
            il,kl=chain[-1]; reach=(8*kl+1)*ur[il]
            if reach>best[0]: best[0]=reach; best[1]=list(chain)
        if len(chain)>=MAXLEN: return
        lastk={}
        for i,k in chain: lastk[i]=max(lastk.get(i,-1),k)
        for i in range(NC):
            for k in range(lastk.get(i,-1)+1, KMAX+1):
                chain.append((i,k)); rec(chain); chain.pop()
                if found: return
            if found: return
    for i in range(NC):
        for k in range(0,KMAX+1):
            rec([(i,k)])
            if found: break
        if found: break
    return found, best, nodes[0]
for (a,b,lab) in ((1.0,7.0,"[1,7]"),):
    for MAXLEN in (6,8,10,12):
        found,best,nodes=search(a,b,KMAX=6,MAXLEN=MAXLEN)
        print(f"  cover {lab}, chains up to length {MAXLEN}, k <= 6: "
              f"{'FEASIBLE' if found else 'infeasible'}   (LP nodes {nodes}, best reach {best[0]:.4f})")
        if found:
            ch,u=found[0]; s=[1/x for x in u]
            print(f"    chain {ch}")
            print(f"    s = {[round(x,4) for x in s]}")
            break
