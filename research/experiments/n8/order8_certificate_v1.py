"""Order 8 finite certificate -- the order-5 method (order5_certificate_v3.py) at n = 8.

Unknowns u_1..u_6 in [1,S] (the six non-nearest readings; the nearest is u = 1, index 0), plus a
margin tau in [0,1].  Every "in the way" and "the instant advances" condition is tightened by tau.
Step 1 maximise tau; tau <= 0 => the word is not strictly realisable, prune.  Step 2 on tau = 0
minimise the last setter's reading; sup R for that word = (8Q+1)/min u.

Finiteness of the word list, from Cascade/Certificate.lean, ALL at general n over the reals:
  cascadeR_zoneHi     R after a setting of x at lap Q is exactly (nQ+1)/u_x
  lap_lt_of_cascadeR_lt   under a cap C a setting has nQ+1 < C*u_x
  lap_lt_of_ratio_le      with u <= S that is Q < (C*S-1)/n, uniform in the arrangement
  laps_strictly_increase  a runner's successive settings carry strictly increasing laps

THE G5 REPAIR.  order5 excludes the nearest runner via nearest_never_sets, which needs C <= n+1.
At n = 8 that is C <= 9 and R reaches ~11.96, so the exclusion is unsound -- PROVENANCE_MAP_v1 G5
records it as FAIL, "the confinement in disguise".  Here the nearest is IN the alphabet, with its
own lap bound from the same inequality at u = 1:  8Q + 1 < C, i.e. Q <= (C-1)//8.  No exclusion.
"""
import sys, itertools
from fractions import Fraction as F
from multiprocessing import Pool
n = 8; th = F(1, n); NU = 6          # u_1..u_6 free; index 0 is the nearest, u = 1

def _lt(p,q): return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])
def simplex_min(A,b,c):
    m=len(A); nv=len(c)
    rows=[]; art=[]
    for i in range(m):
        if b[i] < 0: rows.append(([-a for a in A[i]], -b[i], True))
        else:        rows.append((list(A[i]), b[i], False))
    tot=nv+m+sum(1 for r in rows if r[2])
    T=[]; basis=[]; ai=nv+m
    for i,(a,bb,neg) in enumerate(rows):
        row=[F(0)]*tot
        for j in range(nv): row[j]=a[j]
        row[nv+i]= F(-1) if neg else F(1)
        if neg:
            row[ai]=F(1); basis.append(ai); ai+=1
        else:
            basis.append(nv+i)
        T.append(row+[bb])
    cost=[(F(0),F(0))]*tot
    for j in range(nv): cost[j]=(F(0),c[j])
    for j in range(nv+m,tot): cost[j]=(F(1),F(0))
    for it in range(200000):
        z=[(F(0),F(0))]*tot; obj=(F(0),F(0))
        for i,bi in enumerate(basis):
            cb=cost[bi]
            if cb==(F(0),F(0)): continue
            for j in range(tot):
                z[j]=(z[j][0]+cb[0]*T[i][j], z[j][1]+cb[1]*T[i][j])
            obj=(obj[0]+cb[0]*T[i][tot], obj[1]+cb[1]*T[i][tot])
        ent=-1
        for j in range(tot):
            r=(cost[j][0]-z[j][0], cost[j][1]-z[j][1])
            if _lt(r,(F(0),F(0))): ent=j; break
        if ent<0:
            if obj[0]>0: return None
            x=[F(0)]*nv
            for i,bi in enumerate(basis):
                if bi<nv: x[bi]=T[i][tot]
            return (obj[1], x)
        lv=-1; best=None
        for i in range(len(T)):
            if T[i][ent]>0:
                r=T[i][tot]/T[i][ent]
                if best is None or r<best or (r==best and basis[i]<basis[lv]): best=r; lv=i
        if lv<0: return 'unbounded'
        p=T[lv][ent]; T[lv]=[v/p for v in T[lv]]
        for i in range(len(T)):
            if i!=lv and T[i][ent]!=0:
                f=T[i][ent]; T[i]=[T[i][j]-f*T[lv][j] for j in range(tot+1)]
        basis[lv]=ent

def opt(cons,obj,sense,S,with_tau):
    """cons rows: (a[0..NU-1], at, b) meaning a.u + at*tau <= b.  obj: 0..NU-1 = u index, NU = tau."""
    nv = NU+1 if with_tau else NU
    A=[];b=[]
    for c in cons:
        row=list(c[0])+([c[1]] if with_tau else [])
        A.append(row); b.append(c[2]-sum(c[0]))
    for i in range(NU):
        e=[F(0)]*nv; e[i]=F(1); A.append(e); b.append(F(S-1))
    if with_tau:
        e=[F(0)]*nv; e[NU]=F(1); A.append(e); b.append(F(1))
    cc=[F(0)]*nv; cc[obj]= F(-1) if sense=='max' else F(1)
    r=simplex_min(A,b,cc)
    if r is None or r=='unbounded': return None
    v=r[1][obj]
    return v+1 if obj<NU else v

def coeff(idx,val):
    v=[F(0)]*NU; c=F(0)
    if idx==0: c=val
    else: v[idx-1]=val
    return v,c
def constraints(word):
    cons=[]
    def add(a,at,bb): cons.append((a,at,bb))
    x1,Q1=word[0]
    v,c=coeff(x1,th)
    add(v,F(1),F(Q1)+th-c); add([-t for t in v],F(1),-(F(Q1)-th)+c)
    for j in range(1,len(word)):
        xp,Qp=word[j-1]; xj,Qj=word[j]
        vj,cj=coeff(xj,F(Qp)+th); vp,cp=coeff(xp,F(Qj)); vs,cs=coeff(xp,th)
        add([vj[i]-vp[i]-vs[i] for i in range(NU)],F(1),cs+cp-cj)
        add([-(vj[i]-vp[i])-vs[i] for i in range(NU)],F(1),cs-cp+cj)
    return cons

def extend(word,S,L,L0,DEPTH,best,stats):
    cons=constraints(word); stats[0]+=1
    tau=opt(cons,NU,'max',S,True)
    if tau is None or tau<=0: return
    stats[1]+=1
    x,Q=word[-1]
    m=opt(cons,x-1,'min',S,False) if x>0 else F(1)
    if m is not None and m>0:
        R=F(n*Q+1)/m
        if best[0] is None or R>best[0]: best[0]=R; best[1]=list(word); best[2]=tau
    if len(word)>=DEPTH: stats[2]+=1; return
    used={xx:QQ for xx,QQ in word}
    for nx in range(0,NU+1):
        hi = L0 if nx==0 else L
        for nq in range(used.get(nx,0)+1, hi+1):
            extend(word+[(nx,nq)],S,L,L0,DEPTH,best,stats)

def job(a):
    S,L,L0,DEPTH,first=a
    best=[None,None,None]; stats=[0,0,0]
    extend([first],S,L,L0,DEPTH,best,stats)
    return best,stats

if __name__=='__main__':
    S=int(sys.argv[1]) if len(sys.argv)>1 else 8
    C=int(sys.argv[2]) if len(sys.argv)>2 else 13
    L=(C*S-1)//n; L0=(C-1)//n
    DEPTH=int(sys.argv[3]) if len(sys.argv)>3 else NU*L+L0
    print(f'order 8 certificate: S = {S}, assumed cap C = {C}, lap bound L = {L}, nearest lap bound L0 = {L0}, depth {DEPTH}')
    starts=[(x,q) for x in range(0,NU+1) for q in range(1,(L0 if x==0 else L)+1)]
    with Pool() as p: res=p.map(job,[(S,L,L0,DEPTH,s) for s in starts])
    cand=[b for b,_ in res if b[0] is not None]
    nodes=sum(s[0] for _,s in res); feas=sum(s[1] for _,s in res); trunc=sum(s[2] for _,s in res)
    print(f'   words tested: {nodes}   realisable (max tau > 0): {feas}   truncated at depth: {trunc}')
    if cand:
        best=max(cand,key=lambda b:b[0])
        print(f'   largest sup R over realisable words: {best[0]} = {float(best[0]):.5f}')
        print(f'   word {best[1]}   margin tau = {best[2]}')
        ok = best[0] < C and trunc == 0
        print(f'   self-consistent (sup R < C and no truncation): {ok}')
        print(f'   => Existence PROVED for ratio <= {S} at order 8' if ok else '   => NOT proved at this setting')
    else:
        print('   no realisable word -- the cascade cannot move at this ratio bound')
