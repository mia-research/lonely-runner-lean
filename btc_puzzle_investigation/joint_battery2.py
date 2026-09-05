import sys, math, numpy as np
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from joint_shadow_decompose_v1 import build_U, glv_beta, EPS
from t_y_maxbound_v1 import prime_order_curve, group_coords

def spec(xs,ys,p,n,g):
    xi=np.array(xs[1:],dtype=np.int64); yi=np.array(ys[1:],dtype=np.int64)
    H=np.zeros((p,p),dtype=complex); np.add.at(H,(xi,yi),g)
    return np.fft.fft2(H)

print("p    | GLV(lam correct) | max|U|/sqrt(p)  char / random | #{|U|>4sqrt(p)} char/rand | tail ratio")
for lo,hi in ((160,170),(340,360),(430,440),(570,580),(820,840),(990,1010)):
    r=prime_order_curve(lo,hi)
    if not r: continue
    p,n,G=r; xs,ys=group_coords(G,p,n,0); beta=glv_beta(p)
    U=build_U(xs,ys,p,n,a0=1)
    # --- fix lambda: try BOTH cube roots, report the one that satisfies the identity
    best=None
    for cand in range(2,n):
        if pow(cand,3,n)==1 and cand!=1:
            U2=build_U(xs,ys,p,n,a0=(cand%n))
            e=np.max(np.abs(U2[(beta*np.arange(p))%p,:]-U))
            if best is None or e<best[1]: best=(cand,e)
    A=np.abs(U); A[0,0]=0
    rng=np.random.default_rng(p+1); gr=np.exp(2j*np.pi*rng.random(n-1))
    Ar=np.abs(spec(xs,ys,p,n,gr)); Ar[0,0]=0
    sp=math.sqrt(p)
    mc,mr=A.max()/sp, Ar.max()/sp
    thr=4*sp
    nc,nr=int((A>thr).sum()), int((Ar>thr).sum())
    print(" %-4d| lam=%-5d %.1e | %6.3f / %6.3f            | %6d / %-6d      | %.3f"
          %(p,best[0],best[1],mc,mr,nc,nr,mc/mr))
