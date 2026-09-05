#!/usr/bin/env python3
"""
Does the Moment-Pumping 'decay not grows' verdict account for the CURVE/TWIST?
(2026-07-11, answering the user's question with the confound-controlled discipline.)

Forcing vector (from the RH-programme drafts):  f(p) = chi(p) * p^{-i gamma} * w(p) p^sigma
over primes p<=X.  Concentration = moment ratio  MR = ||f^perp||_8 / ||f^perp||_2
(spike -> 1; delocalized/random -> ~ N^{-3/8} ~ X^{-0.36}, the 'decay' verdict).

The drafts tested MR over (X, gamma, sigma, chi) with GENERIC Dirichlet chi and
found DECAY (delocalization) -> Moment-Pumping FALSE.  User's question: with the
CM/curve twist, would it look like GROWTH (concentration)?

Mechanism to test: the CM Hecke twist uses a_p, which is ZERO on inert primes
(chi_-3(p)=-1) -> the vector is supported on SPLIT primes only (half) AND weighted
by |a_p| (Sato-Tate) -> both raise concentration -> MR decays SLOWER / looks like
growth.  BUT that concentration is the PUBLIC chi_-3 conductor support, not a zero.
CONTROL: restrict to split primes (remove the a_p=0 support).  If the CM excess
concentration then collapses to the generic decay, the 'growth' is the conductor
shadow (false positive), NOT a repair of the forcing.

Twists compared (all with the same gamma, sigma, envelope, projection):
  trivial   chi(p)=1
  dirichlet a generic quadratic Dirichlet character mod a prime q0
  chi_-3    the CM quadratic character (p mod 3)
  CM a_p    the Hecke twist a_p (=0 on inert)  <-- the curve's twist
  CM split  CM a_p but restricted to SPLIT primes only (control)
"""
import numpy as np, math
rng=np.random.default_rng(0)

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]
PALL=sieve(600000)
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
def chi3(p): return 0 if p%3==0 else (1 if p%3==1 else -1)

q0=101
# a real (quadratic) Dirichlet character mod q0
def chiq(p): return 0 if p%q0==0 else (1 if pow(p%q0,(q0-1)//2,q0)==1 else -1)

gamma=14.13; sigma=0.5
def forcing_vector(X, kind):
    ps=[p for p in PALL if 7<p<=X]
    f=[]
    for p in ps:
        env = p**sigma * math.exp(-p/X)           # w_X(p) p^sigma : spread over large primes
        ph  = np.exp(-1j*gamma*math.log(p))
        if kind=="trivial":   c=1.0
        elif kind=="dirichlet": c=chiq(p)
        elif kind=="chi_-3":  c=chi3(p)
        elif kind in ("cm","cm_split"):
            a=a_ell(p); c=a/(2*math.sqrt(p))       # normalized Sato-Tate weight (0 on inert)
        f.append(c*ph*env)
    f=np.array(f,dtype=complex)
    if kind=="cm_split":
        mask=np.array([a_ell(p)!=0 for p in ps])   # keep only split primes (a_p != 0)
        f=f[mask]
    return f

def MR(f, r=5):
    # project out a rank-r smooth subspace (constant + low log-freq modes) then MR_8/2
    n=len(f); idx=np.arange(n)
    B=np.array([np.ones(n)]+[np.cos((k+1)*np.pi*idx/n) for k in range(r-1)]).T.astype(complex)
    Q,_=np.linalg.qr(B)
    fp=f-Q@(Q.conj().T@f)
    two=np.linalg.norm(fp)
    if two==0: return 0.0
    eight=(np.sum(np.abs(fp)**8))**(1/8)
    return eight/two

Xs=[1000,2000,4000,8000,16000,32000]
print(f"gamma={gamma}, sigma={sigma}.  MR = ||f^perp||_8/||f^perp||_2 (spike->1, random->X^-0.36)\n")
print(f"{'kind':>10} | " + "  ".join(f"X={X:<5}" for X in Xs) + " | slope(logMR vs logX)")
for kind in ("trivial","dirichlet","chi_-3","cm","cm_split"):
    mrs=[MR(forcing_vector(X,kind)) for X in Xs]
    lx=np.log(Xs); ly=np.log(mrs)
    slope=np.polyfit(lx,ly,1)[0]
    print(f"{kind:>10} | " + "  ".join(f"{m:<7.4f}" for m in mrs) +
          f" | {slope:+.3f}  {'CONCENTRATES/grows' if slope> -0.15 else 'delocalizes/decays'}")

print("\nRead-out:")
print(" trivial/dirichlet/chi_-3 slope ~ -0.36 = DELOCALIZE (the drafts' decay verdict).")
print(" If CM slope >> -0.36 (concentrates) BUT cm_split returns to ~ -0.36, then the")
print(" 'twist looks like growth' is REAL but is the chi_-3 conductor SUPPORT (a_p=0 on")
print(" inert) -- a public null structure, NOT a genuine zero-forcing signal. It would")
print(" be a FALSE POSITIVE for the forcing, not a repair (same conductor-shadow trap).")
