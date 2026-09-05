"""
N8 REDUCTION -- machine-check of the full chain.  Exact integers only.

CORE LEMMA (verified separately, pencil_vanishing_v1.py):
    n odd  =>  Sp(R) - I(R) = 1   for every R != O.

CLAIMED CHAIN (hand-derived; checked here):
  (a) Sp(R) = (h1(R)+1)/2   for R != O,   h1(R) = sum_{P != O,R} chi2(y_P y_{R-P})
  (b) h1(O) = (n-1)*chi                                   chi = chi2(-1)
  (c) I(O)  = -chi*(2p+1-n)/2
        [ Frob Q = -Q  =>  y_Q^{p-1} = -1  =>  chi2^{(2)}(y_Q) = (-1)^{(p+1)/2} = -chi,
          and #{Q : Frob Q = -Q} = #E'(F_p) = 2p+2-n  (quadratic twist) ]
  (d) => V1^2 - V2 = (n-1)chi - 2 I(O) = 2*chi*p      <-- the identity M21/P19
"""
import sys
sys.path.insert(0, 'scratchpad/n8')
from pencil_vanishing_v1 import leg, pts, add, neg, m2, s2, n2, i2, pw2, add2, frob

def check(p, A, B):
    E = pts(p, A, B); n = len(E)+1; chi = leg(-1, p)
    r = next(u for u in range(2, p) if leg(u, p) == -1)
    sq = {}
    for y0 in range(p):
        for y1 in range(p): sq.setdefault(m2((y0,y1),(y0,y1),p,r), []).append((y0,y1))
    E2 = []
    for x0 in range(p):
        for x1 in range(p):
            x=(x0,x1); x3=m2(m2(x,x,p,r),x,p,r)
            rhs=s2(s2(x3,(A*x0%p,A*x1%p),p),(B,0),p)
            for y in sq.get(rhs,()): E2.append((x,y))
    E2only=[Q for Q in E2 if not (Q[0][1]==0 and Q[1][1]==0)]
    EXP2=(p*p-1)//2
    chi2_2 = lambda z: 1 if pw2(z, EXP2, p, r) == (1,0) else -1

    ok = {}
    # (a) and the core lemma, all R != O
    a_ok = lem_ok = True
    for R in E:
        h1 = 0
        for P in E:
            Pp = add(R, neg(P,p), p, A)
            if Pp is None: continue
            h1 += leg(P[1],p)*leg(Pp[1],p)
        Sp = 0; seen=set()
        for P in E:
            Pp = add(R, neg(P,p), p, A)
            if Pp is None: continue
            k = tuple(sorted([P,Pp]))
            if k in seen: continue
            seen.add(k); Sp += leg(P[1],p)*leg(Pp[1],p)
        I = 0
        for Q in E2only:
            Nm = add2(Q, frob(Q,p), p, A, r)
            Rq = None if Nm is None else (Nm[0][0], Nm[1][0])
            if Rq == R: I += chi2_2(Q[1])
        I //= 2
        if Sp != (h1+1)//2 or 2*Sp != h1+1: a_ok = False
        if Sp - I != 1: lem_ok = False
    ok['(a) Sp=(h1+1)/2'] = a_ok
    ok['CORE Sp-I=1']     = lem_ok

    # (b) h1(O)
    h1O = 0
    for P in E:
        Pm = neg(P,p)
        h1O += leg(P[1],p)*leg(Pm[1],p)
    ok['(b) h1(O)=(n-1)chi'] = (h1O == (n-1)*chi)

    # (c) I(O)
    IO = 0; cnt = 0
    for Q in E2only:
        Nm = add2(Q, frob(Q,p), p, A, r)
        if Nm is None:
            cnt += 1; IO += chi2_2(Q[1])
    IO //= 2; cnt //= 2
    ok['(c) I(O)=-chi(2p+1-n)/2'] = (IO == -chi*(2*p+1-n)//2) and (2*cnt == 2*p+1-n)

    # (d) the identity itself, all a, via V1,V2 in Z[zeta_n]
    G = None
    for c in E:
        T=c; k=1
        while T is not None: T=add(T,c,p,A); k+=1
        if k==n: G=c; break
    d_ok = None
    if G is not None:
        dl={}; T=G
        for k in range(1,n): dl[T]=k; T=add(T,G,p,A)
        dlg = lambda X: 0 if X is None else dl[X]
        res=[]
        for aa in range(1,n):
            V1=[0]*n
            for P in E: V1[(aa*dl[P])%n] += leg(P[1],p)
            V2=[0]*n
            for Q in E2:
                if Q[1]==(0,0): continue
                if Q[0][1]==0 and Q[1][1]==0:
                    c2=1; Nm=add(( Q[0][0],Q[1][0]),(Q[0][0],Q[1][0]),p,A)
                else:
                    c2=chi2_2(Q[1]); N=add2(Q,frob(Q,p),p,A,r)
                    Nm=None if N is None else (N[0][0],N[1][0])
                V2[(aa*dlg(Nm))%n] += c2
            w=[0]*n
            for i,u in enumerate(V1):
                if u:
                    for j,v in enumerate(V1):
                        if v: w[(i+j)%n]+=u*v
            for i in range(n): w[i]-=V2[i]
            w[0]-=2*chi*p
            res.append(len(set(w))<=1)          # ==0 in Z[zeta_n]
        d_ok=f"{sum(res)}/{len(res)}"
    ok['(d) V1^2-V2=2chi p']=d_ok
    print(f"p={p:3d} A={A} B={B} n={n:3d} chi={chi:+d} | " +
          " | ".join(f"{k}:{v}" for k,v in ok.items()), flush=True)

for (p,A,B) in [(11,0,4),(13,0,1),(17,1,5),(19,0,3),(19,3,1),(23,1,4),(29,2,1)]:
    if (len(pts(p,A,B))+1) % 2 == 1: check(p,A,B)
