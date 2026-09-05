#!/usr/bin/env python3
"""
Spectrum-dilution check (2026-07-11).  Claim under test:
    lambda_max(G_Q) / Tr(G_Q) = O(1/log Q),  depends only on Q, not on X.

The user's two flags (both tested here):
  (i)  "naive Gram vs off-diagonal correlations" -- lambda_max/Tr can shrink for a
       TRIVIAL reason (Tr grows as you add features) while the off-diagonal common
       mode PERSISTS.  So track lambda_max ABSOLUTE, lambda_2, and the independent-
       feature (Marchenko-Pastur) floor, not just the ratio.
  (ii) "residue shadows of the same conductor" -- the top mode may be the shared
       chi_-3 / conductor structure across all residue features, not a CM spectral
       gap.  Test: align top eigenvector with the conductor direction; project it
       out; re-measure.

Construction (faithful to the ZFR low-prime-feature Gram):
  sample  = first X good primes ell (ell not | 42).
  CM Hecke variable  x_ell = a_ell / (2 sqrt ell) = cos(theta_ell)  (0 for inert).
  feature at prime q<=Q (q not|42):  f_q(ell) = Legendre(ell/q), CENTERED over the sample.
  CM-coupled feature:  g_q(ell) = x_ell * f_q(ell).
  G_Q[q,q'] = (1/X) sum_ell g_q(ell) g_{q'}(ell)      (raw covariance; Tr = total variance)
  ratio = lambda_max(G_Q) / Tr(G_Q).

CONTROLS (matched X, Q, marginals):
  C0  raw residue Gram (no CM weight): g_q = f_q  -> pure residue features.
  C1  shuffle x_ell across samples (kills CM<->residue coupling, keeps x-marginal).
  C2  x_ell -> random +-1 with same nonzero pattern (kills CM, keeps sparsity).
  C3  x_ell from a NON-CM curve (y^2=x^3-x^2-2x-1? use a known non-CM: '389a' a_ell)
      -- here approximated by a generic curve b: y^2=x^3+x (j=1728 CM) vs a true
      non-CM; we use a random-sign proxy as the clean null (C2) and report.
  MP  Marchenko-Pastur edge for independent features: lambda_max ~ sigma^2(1+sqrt(d/X))^2,
      ratio_MP ~ (1+sqrt(d/X))^2 / d.
"""
import numpy as np, math
np.random.seed(11)

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]

UNITS=[(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
IDX2POW={0:0,1:3,2:2,3:5,4:4,5:1}; POW2IDX={v:k for k,v in IDX2POW.items()}
def mulw(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Trw(v): return 2*v[0]-v[1]
def conj(v): return (v[0]-v[1],-v[1])
def primary(v):
    for u in UNITS:
        w=mulw(u,v)
        if w[0]%3==2 and w[1]%3==0: return w
def cornacchia(l):
    for y in range(1,int((4*l/3)**.5)+2):
        d=4*l-3*y*y
        if d<0: break
        s=int(d**.5)
        if s*s==d and (s+y)%2==0: return ((s+y)//2,y)
def u_of(l,pip):
    pc=conj(pip); w=(-pc[0]*pow(pc[1],-1,l))%l
    tab={(u[0]+u[1]*w)%l:i for i,u in enumerate(UNITS)}
    s=pow(28%l,(l-1)//6,l)
    return POW2IDX[(IDX2POW[tab[s]]+3)%6]
def a_ell(l):
    if l in (2,3,7) or l%3==2: return 0
    p=primary(cornacchia(l)); return Trw(mulw(UNITS[u_of(l,p)],p))
def legendre(a,q):
    a%=q
    if a==0: return 0
    r=pow(a,(q-1)//2,q)
    return 1 if r==1 else -1

PR=sieve(200000)
good=[l for l in PR if l>7 and 42%l!=0][:2500]     # sample primes (features are along these)
x_all=np.array([a_ell(l)/(2*math.sqrt(l)) for l in good])   # CM Hecke Sato-Tate var

a_all=np.array([a_ell(l) for l in good],dtype=float)   # raw Hecke eigenvalues

def features(Xn, Q, kind):
    ells=good[:Xn]; qs=[q for q in PR if q<=Q and 42%q!=0]
    if kind=="legendre":     # residue of ELL at q -- asymptotically INDEPENDENT across q
        F=np.array([[legendre(l,q) for q in qs] for l in ells],dtype=float)
    elif kind=="ares":       # residue of the HECKE EIGENVALUE a_ell at q -- shadows of ONE a_ell
        F=np.array([[legendre(int(a_all[j]),q) for q in qs] for j,l in enumerate(ells)],dtype=float)
    F-=F.mean(axis=0,keepdims=True)
    return F, qs

def build_ratio(Xn, Q, mode="CM", kind="legendre"):
    x=x_all[:Xn].copy()
    F,qs=features(Xn,Q,kind)
    if mode=="CM":       w=x
    elif mode=="C0":     w=np.ones(Xn)
    elif mode=="C1":     w=np.random.permutation(x)
    elif mode=="C2":     w=np.where(x!=0, np.random.choice([-1,1],Xn), 0.0)
    G=(F*w[:,None]).T@(F*w[:,None])/Xn
    ev=np.linalg.eigvalsh(G)[::-1]
    return dict(lmax=ev[0], l2=ev[1] if len(ev)>1 else 0.0, tr=ev.sum(),
                ratio=ev[0]/ev.sum(), d=len(qs), ev=ev)

print("=== reproduce the table: lambda_max/Tr, CM, vs X and Q ===")
print(f"{'':6} " + "".join(f"Q={q:<8}" for q in (5,10,20,50)))
for Xn in (500,1000,1500,2000):
    row=[build_ratio(Xn,q,"CM")["ratio"] for q in (5,10,20,50)]
    print(f"X={Xn:<4} " + "".join(f"{r:<10.3f}" for r in row))

print("\n=== the diagnostic: is the dilution a real gap, or Tr-growth + conductor shadow? ===")
print("(X=2000 fixed)")
print(f"{'Q':>4} {'d':>3} | {'CM ratio':>8} {'lmax(abs)':>10} {'l2(abs)':>8} {'lmax/l2':>7} "
      f"| {'C0 resid':>8} {'C2 rand':>8} {'MP floor':>8}")
for Q in (5,10,20,50,100,200):
    cm=build_ratio(2000,Q,"CM"); c0=build_ratio(2000,Q,"C0"); c2=build_ratio(2000,Q,"C2")
    d=cm["d"]; mp=(1+math.sqrt(d/2000))**2/d * (cm["tr"]/d)/ (cm["tr"]/d)  # ratio_MP ~ (1+sqrt(d/X))^2/d
    mp_ratio=(1+math.sqrt(d/2000))**2/d
    print(f"{Q:>4} {d:>3} | {cm['ratio']:>8.3f} {cm['lmax']:>10.4f} {cm['l2']:>8.4f} "
          f"{cm['lmax']/max(cm['l2'],1e-9):>7.2f} | {c0['ratio']:>8.3f} {c2['ratio']:>8.3f} {mp_ratio:>8.3f}")

print("\n=== SAME features but residues of a_ell (shadows of ONE conductor) ===")
print(f"{'Q':>4} {'d':>3} | {'C0 ratio':>8} {'lmax(abs)':>10} {'lmax/l2':>7}  (a_ell-residue features)")
for Q in (5,10,20,50,100,200):
    r=build_ratio(2000,Q,"C0",kind="ares")
    print(f"{Q:>4} {r['d']:>3} | {r['ratio']:>8.3f} {r['lmax']:>10.4f} {r['lmax']/max(r['l2'],1e-9):>7.2f}")

print("\n=== conductor-shadow test: top eigenvector alignment + project-out ===")
# does the top mode align with the conductor (chi_-3) direction? Build the")
# common direction from x itself (the CM Hecke imprint) projected to feature space.
for Q in (10,50,200):
    x=x_all[:2000]
    F,qs=features(2000,Q,"ares")
    G=(F).T@(F)/2000    # a_ell-residue features, unweighted (the conductor-shadow regime)
    ev,evec=np.linalg.eigh(G); ev=ev[::-1]; evec=evec[:,::-1]
    top=evec[:,0]
    # conductor direction: correlation of each feature q with the raw CM variable x
    #   c_q = corr(x, f_q)  -> the 'chi_-3 shadow' loading of feature q
    cshadow=np.array([np.corrcoef(x, F[:,i])[0,1] for i in range(len(qs))])
    cshadow/=np.linalg.norm(cshadow)+1e-12
    align=abs(np.dot(top,cshadow))
    # project out the common (conductor) mode, re-measure ratio
    P=np.eye(len(qs))-np.outer(cshadow,cshadow)
    Gp=P@G@P; evp=np.linalg.eigvalsh(Gp)[::-1]
    print(f"Q={Q:>3} d={len(qs):>3}: |<top eigvec, conductor-shadow dir>| = {align:.3f}; "
          f"ratio before={ev[0]/ev.sum():.3f}  after proj-out={evp[0]/max(evp.sum(),1e-9):.3f}")

print("\nRead-out:")
print(" - If CM ratio >> C2/MP floor and lmax(abs) ~ flat while Tr grows => dilution is")
print("   Tr-GROWTH (feature counting), NOT a closing gap; the top mode PERSISTS.")
print(" - If |align| ~ 1 and ratio collapses after projecting the conductor mode out =>")
print("   the top mode IS the chi_-3 / conductor shadow (residue shadows of one conductor).")
