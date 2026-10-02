import sys
from fractions import Fraction as F
sys.argv=[sys.argv[0],"0"]
exec(open('residual_anatomy_v1.py').read().split('if __name__')[0])
def anatomy(S):
    S=sorted(S); print("S =",S, " residual:",residual(tuple(S)))
    path=cascade(S); print("cascade states:",[str(p) for p in path])
    t=path[-1]
    # identify landing as (8k+1)/(8b)
    cands=[(b,(t*8*b-1)/8) for b in S if (t*8*b-1)/8==int((t*8*b-1)/8)]
    print("landing t =",t,"= (8k+1)/(8b) for (b,k) in",[(b,int(k)) for b,k in cands])
    print("all certificates (b,k<b):",allcerts(S))
    b,k=cands[0][0],int(cands[0][1])
    print("\nlanding flank b=%d, lap k=%d.  position(eighths) = q + eps + 8*{k*eps}  (mod 8)"%(b,k))
    print(" a   q=a//b  r=a%b  eps=r/b   {k eps}     q+eps+8{k eps}   mod 8     clear-margin(eighths beyond edge)")
    for a in S:
        q,r=divmod(a,b); eps=F(r,b); fr=(k*eps)%1
        pos=(q+eps+8*fr)%8
        m=min(pos,8-pos)-1
        print(" %-3d %-7d %-6d %-8s %-9s %-16s %-9s %s"%(a,q,r,eps,fr,q+eps+8*fr,float(pos),float(m)))
    print("\nstates visited (b,k) with blockers:")
    t=F(1,8*min(S))
    for step in range(len(path)):
        bl=[d for d in S if cd(d*t)<F(1,8)]
        print("  t=%s  blockers=%s"%(t,bl))
        if not bl: break
        nxt=[(F(8*round(d*t)+1,8*d),d,round(d*t)) for d in bl]
        t,d,kk=max(nxt); print("     -> opening of %d lap %d  (8*%d+1)/(8*%d)"%(d,kk,kk,d))
anatomy([1,2,3,5,7,12,16])

def moves(S):
    S=sorted(S); path=cascade(S)
    print("\nper move: position (eighths mod 8) before, shift 8*x*dt (eighths), position after; * = in the way after")
    for t0,t1 in zip(path,path[1:]):
        dt=t1-t0; print(" move %s -> %s  dt=%s (%.4f)"%(t0,t1,dt,float(dt)))
        for x in S:
            p0=(8*x*t0)%8; sh=8*x*dt; p1=(8*x*t1)%8
            blk = min(p1,8-p1)<1
            print("    x=%-3d before %-7.3f shift %-7.3f after %-7.3f %s"%(x,float(p0),float(sh),float(p1),"*" if blk else ""))
moves([1,2,3,5,7,12,16])
