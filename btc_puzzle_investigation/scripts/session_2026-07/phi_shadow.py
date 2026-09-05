"""
phi(n) SHADOW test on the 82 real keys.

Why phi(n): a hint about n collapses k into the phi(n) residues coprime to n
(v1 sec.2). So the shadow to look for is in the COPRIMALITY structure -- does the
public key, reduced mod n, behave like a unit of Z_n at a rate that departs from
phi(n)/n?  Equivalently: is (X,Y) "aware" of n's multiplicative structure?

Two parts:
  [1] UNIT-RATE SHADOW. For V in {X, Y, XY, X+Y}, count how often V mod n is a
      unit (gcd=1). Expected under the ECDLP-flat null (V mod n ~ uniform in Z_n)
      = sum phi(n)/n. Report a Poisson-binomial z. CRITICAL CONTROL: recompute
      with n replaced by n-2..n+2 (numbers with no role in the construction). If
      the true-n statistic is not an outlier among its neighbors, any "shadow" is
      about arithmetic-in-general, not about the key's n. (This is the control
      that flagged the v2 gcd(Y,n) flicker as noise -- it sign-flipped at n+/-1.)

  [2] DIRECT phi(n) LEAK. Target = phi(n)/n ratio bucket and phi(n) mod 3, hunted
      from the X / Y / XY channels (best-feature MI + permutation null), same
      machinery as the n/k hunt.

Real keys only; nulls are permutations / parametric. Nothing fabricated.
"""
import csv, math
from math import gcd
import numpy as np

def phi(n):
    r=n; t=n; p=2
    while p*p<=t:
        if t%p==0:
            while t%p==0: t//=p
            r-=r//p
        p+=1
    if t>1: r-=r//t
    return r

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['X'],16),int(r['Y'],16),int(r['n']),int(r['k'])))
Xs=[x for x,_,_,_ in rows]; Ys=[y for _,y,_,_ in rows]
n =np.array([nn for _,_,nn,_ in rows]); k=np.array([kk for _,_,_,kk in rows]); M=len(rows)

# ---------- [1] unit-rate / coprimality shadow ----------
def channel_vals(name, mod_arr):
    out=[]
    for i in range(M):
        m=int(mod_arr[i])
        if m<2: out.append((0,m)); continue
        if name=="X":   v=Xs[i]%m
        elif name=="Y": v=Ys[i]%m
        elif name=="XY":v=(Xs[i]*Ys[i])%m
        else:           v=(Xs[i]+Ys[i])%m
        out.append((v,m))
    return out

def unit_z(name, mod_arr):
    obs=0; exp=0.0; var=0.0
    for v,m in channel_vals(name, mod_arr):
        if m<2: continue
        pu=phi(m)/m
        # correct null P(channel is a unit mod m): a PRODUCT needs both factors
        # coprime -> (phi/m)^2; X, Y, and the sum X+Y are each uniform -> phi/m.
        p = pu*pu if name=="XY" else pu
        is_unit=1 if gcd(v,m)==1 else 0
        obs+=is_unit; exp+=p; var+=p*(1-p)
    z=(obs-exp)/math.sqrt(var) if var>0 else 0.0
    return obs,exp,z

print("=== [1] unit-rate shadow: is (channel mod n) a unit more/less than phi(n)/n? ===")
print(f"{'channel':>6} | {'obs':>4} | {'exp':>6} |   z    |  z at n-2..n+2 (control)")
for name in ("X","Y","XY","X+Y"):
    o,e,z=unit_z(name,n)
    ctrl=[round(unit_z(name,n+dd)[2],2) for dd in (-2,-1,1,2)]
    star=" *" if abs(z)>2 else ""
    print(f"{name:>6} | {o:>4} | {e:6.2f} | {z:+5.2f}{star} | {ctrl}")
print("   read: a real n-shadow => |z| large at n AND small at all of n-2..n+2.")

# ---------- [2] direct phi(n) leak from X / Y / XY ----------
phis=np.array([phi(int(nn)) for nn in n])
ratio_bucket=np.clip((phis/n*4).astype(int),0,3)     # phi/n in quartiles
targets={"phi/n-quartile":ratio_bucket, "phi(n)%3":(phis%3)}

_PR=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61)
def build(kind):
    F={}
    if kind=="XY":
        for m in _PR:
            F[f"XY%{m}"]=np.array([(x*y)%m for x,y in zip(Xs,Ys)])
            F[f"X+Y%{m}"]=np.array([(x+y)%m for x,y in zip(Xs,Ys)])
        for p in (3,5,7,11,13,17,19,23):
            F[f"XYleg{p}"]=np.array([pow((x*y)%p,(p-1)//2,p) for x,y in zip(Xs,Ys)])
    else:
        V=Xs if kind=="X" else Ys
        for m in _PR: F[f"{kind}%{m}"]=np.array([v%m for v in V])
        for p in (3,5,7,11,13,17,19,23): F[f"{kind}leg{p}"]=np.array([pow(v%p,(p-1)//2,p) for v in V])
    return F
def mi(f,t):
    A=int(f.max())+1;B=int(t.max())+1;j=np.zeros((A,B))
    for a,b in zip(f,t): j[a,b]+=1
    j/=j.sum();pa=j.sum(1,keepdims=True);pb=j.sum(0,keepdims=True)
    with np.errstate(divide='ignore',invalid='ignore'):
        term=j*np.log2((j+1e-30)/(pa*pb+1e-30))
    return float(term[j>0].sum())
rng=np.random.default_rng(3)
def channel_p(F,t,iters=3000):
    def bm(tt): return max(mi(c,tt) for c in F.values())
    obs=bm(t);c=1
    for _ in range(iters):
        if bm(rng.permutation(t))>=obs: c+=1
    return obs,c/(iters+1)

print("\n=== [2] direct phi(n) leak (best-feature MI + perm null) ===")
print(f"{'target':>15} | {'chan':>3} | MI(bits) | perm-p")
chans={k:build(k) for k in ("X","Y","XY")}
for tn,t in targets.items():
    for cn,F in chans.items():
        o,p=channel_p(F,t)
        print(f"{tn:>15} | {cn:>3} |  {o:6.4f} | {p:5.3f}{' *' if p<0.05 else ''}")
