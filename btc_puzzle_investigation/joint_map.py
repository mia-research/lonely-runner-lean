import sys, math, numpy as np
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from joint_shadow_decompose_v1 import build_U, glv_beta
from t_y_maxbound_v1 import prime_order_curve, group_coords

def find_lambda(p,n,beta,xs,ys,U):
    best=None
    for c in range(2,n):
        if pow(c,3,n)==1 and c!=1:
            U2=build_U(xs,ys,p,n,a0=(c%n))
            e=np.max(np.abs(U2[(beta*np.arange(p))%p,:]-U))
            if best is None or e<best[1]: best=(c,e)
    return best[0]

for lo,hi in ((160,170),(340,360),(430,440),(570,580),(820,840)):
    r=prime_order_curve(lo,hi)
    if not r: continue
    p,n,G=r; xs,ys=group_coords(G,p,n,0); beta=glv_beta(p); sp=math.sqrt(p)
    U=build_U(xs,ys,p,n,a0=1)            # a0=1 fixed
    lam=find_lambda(p,n,beta,xs,ys,U)
    print("\n===== p=%d n=%d beta=%d lambda=%d ====="%(p,n,beta,lam))

    # (1) EVEN/ODD split of U by the exact parity identity U(-a,b,c)=U(a,b,-c).
    # Even-in-c part: Ue=(U(b,c)+U(b,-c))/2 ; Odd part Uo=(U(b,c)-U(b,-c))/2.
    cflip=(-np.arange(p))%p
    Ue=0.5*(U+U[:,cflip]); Uo=0.5*(U-U[:,cflip])
    Ae,Ao=np.abs(Ue),np.abs(Uo); Ae[0,0]=0
    te,to=(Ae**2).sum(),(Ao**2).sum()
    print("  ENERGY  even(c)=%.4f  odd(c)=%.4f   (odd = the y-supplied half)"%(te/(te+to),to/(te+to)))
    # the odd half lives entirely off the c=0 line by construction:
    print("  odd-half mass on c=0 line: %.2e (must be ~0)  |  even-half off c=0: %.4f"
          %((Ao[:,0]**2).sum()/to, 1-(Ae[:,0]**2).sum()/te))

    # (1b) GLV grading of the ODD half's support: is |Uo| constant on GLV orbits (b -> beta b)?
    # orbit of columns under b->beta*b (a is fixed=1 so rows shift by lam, but we look at (a=1 row)).
    # Full-array GLV check on odd half: Uo should satisfy Uo(a lam,b beta)=Uo(a,b) too (parity commutes w GLV)
    Uo2=0.5*(build_U(xs,ys,p,n,a0=lam%n)+build_U(xs,ys,p,n,a0=lam%n)[:,cflip])  # even part at a=lam..
    # test odd part GLV:
    Uo_lam=0.5*(build_U(xs,ys,p,n,a0=lam%n)-build_U(xs,ys,p,n,a0=lam%n)[:,cflip])
    glv_odd=np.max(np.abs(Uo_lam[(beta*np.arange(p))%p,:]-Uo))
    print("  GLV on ODD half  |Uo(a lam,b beta)=Uo(a,b)| err=%.2e (exact => odd half is ALSO mu6-graded)"%glv_odd)

    # (2) T_y MAX-BOUND corner: max over (b,c) of |U|, and specifically the ODD half max.
    # avg|U|^2 = n is proven; the question is whether max_o is O(sqrt(p)) uniformly or spikes.
    print("  MAX  |U|/sqrt(p)=%.3f   |Uodd|/sqrt(p)=%.3f   |Ueven|/sqrt(p)=%.3f  (Weil ceiling 4.0)"
          %(np.abs(U)[1:].max()/sp, Ao.max()/sp, Ae[1:].max()/sp))
    # where is the odd-half max? is the (b,c) achieving it GLV/arithmetically special?
    bmax,cmax=np.unravel_index(np.argmax(Ao),Ao.shape)
    print("  odd-half argmax at (b=%d,c=%d)  b/c mod grading: b*inv(c) mod p = %s"
          %(bmax,cmax, (bmax*pow(int(cmax),p-2,p))%p if cmax else "c=0"))

    # (3) PHASE of the odd half: arg(Uo) — does it carry a GLV/Frobenius phase the magnitude hides?
    # test: is arg(Uo(a lam,b beta)) - arg(Uo(a,b)) a constant (a pure phase char) or random?
    m=Ao>0.3*sp
    ph=np.angle(Uo_lam[(beta*np.arange(p))%p,:][m])-np.angle(Uo[m])
    ph=np.mod(ph+np.pi,2*np.pi)-np.pi
    print("  odd-half PHASE under GLV: mean=%.3f std=%.3f  (std~0 => rigid phase; std~1.8 => random)"
          %(ph.mean(),ph.std()))
