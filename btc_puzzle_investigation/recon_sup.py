# Does the char-vs-random control behave DIFFERENTLY under rho_inf than under rho2?
# rho2 is already known GENERIC (char 0.9996 vs random 0.9997). rho_inf was never computed
# for the random target. Same code path, one extra normalization. Nothing else changed.
import sys, math, numpy as np
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from joint_shadow_decompose_v1 import (build_U, joint_mask, sep_mask, glv_beta, EPS)
from t_y_maxbound_v1 import prime_order_curve, group_coords

def recon_both(xs, ys, p, n, g, mask):
    xi=np.array(xs[1:],dtype=np.int64); yi=np.array(ys[1:],dtype=np.int64)
    H=np.zeros((p,p),dtype=complex); np.add.at(H,(xi,yi),g)
    V=np.fft.fft2(H); m=mask&(np.abs(V)>EPS)
    Fh=np.zeros_like(V); Fh[m]=V[m]/np.abs(V[m]); Fh[0,0]=0.0
    Fd=(np.fft.ifft2(Fh)*(p*p))[xi,yi]
    corr=np.mean(Fd*np.conj(g))
    l2  =math.sqrt(float(np.mean(np.abs(Fd)**2))) or 1e-18
    linf=float(np.max(np.abs(Fd))) or 1e-18
    gn  =math.sqrt(float(np.mean(np.abs(g)**2))) or 1e-18
    return abs(corr)/(l2*gn), abs(corr)/(linf*gn)

print(" p    |          rho2 (known GENERIC)     |            rho_inf (NEW)")
print("      |   char     random    |diff|       |   char     random    |diff|    verdict")
for lo,hi in ((160,170),(340,360),(430,440),(570,580)):
    r=prime_order_curve(lo,hi)
    if not r: continue
    p,n,G=r
    xs,ys=group_coords(G,p,n,0)
    w1=np.exp(2j*np.pi*np.arange(1,n)/n)
    rng2=np.random.default_rng(p+1); g_rand=np.exp(2j*np.pi*rng2.random(n-1))
    jm=joint_mask(p)
    c2,ci=recon_both(xs,ys,p,n,w1,jm)
    r2,ri=recon_both(xs,ys,p,n,g_rand,jm)
    v = "GENERIC" if abs(ci-ri)<0.03 else "*** CHAR-SPECIFIC ***"
    print(" %-5d| %.4f   %.4f   %.4f     | %.4f   %.4f   %.4f   %s"
          %(p,c2,r2,abs(c2-r2),ci,ri,abs(ci-ri),v))
