#!/usr/bin/env python3
"""
Ultrathink probe (2026-07-11): does the mu_3 (cubic) part of the order-6
Grossencharacter EVER carry a real spectral correlation, or is only mu_2 = chi_-3
(the quadratic part) ever visible?

Established: the ONE real CM common mode is the rank-1 chi_-3 shadow, from a_ell=0
on INERT primes (a support/vanishing effect).  chi_-3 = chi^3 (quadratic part of
the sextic chi).  Question: where is mu_3 (cubic, chi^2)?

Test on SPLIT primes only (a_ell != 0, so the chi_-3 support effect is gone):
  build feature correlations from
    (P)  the Grossencharacter PHASE u_ell = chi(ell) in mu_6  (the full sextic)
    (C)  the CUBIC residue symbol  chi3q(ell) = (ell/q)_3  across primes q
    (S)  Sym^2 data  a_{ell^2} = a_ell^2 - ell  (where the cubic chi^2 lives:
         L(Sym^2 E,s) = L(psi^2,s) L(chi_-3,s-1), psi^2 has finite char chi^2)
  and check each for a genuine common mode vs a MATCHED SHUFFLE NULL + alignment
  with the cubic direction.

Prediction A (Thread II): cubic shows a genuine mode in Sym^2 (rank ~ |mu3|=3-ish).
Prediction B (Thread IV): NO cubic/sextic mode at any order -- only chi_-3 (from
  supersingular vanishing) is ever real; the cubic/sextic are equidistributed
  phases, spectrally invisible.  (a_ell REAL => cannot see a pure phase.)
"""
import numpy as np, math
rng=np.random.default_rng(3)

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]
PRIMES=sieve(500000)
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
def cubic_sym(a,q):     # cubic residue symbol (a/q)_3 in mu_3 (q==1 mod 3), as index 0/1/2
    if a%q==0: return None
    v=pow(a%q,(q-1)//3,q)
    # map to 0,1,2 by matching powers of a fixed cube root
    for e in range(3):
        if pow(2,e*(q-1)//3,q)==v: return e
    return 0

SPLIT=[l for l in PRIMES if l>7 and l%3==1][:1500]
aL={l:a_ell(l) for l in SPLIT}
uL={l:u_of(l,primary(cornacchia(l))) for l in SPLIT}   # unit index in mu_6

def corr_stats(F, label):
    F=F-F.mean(0,keepdims=True)
    nrm=np.linalg.norm(F,axis=0,keepdims=True); nrm[nrm==0]=1; F=F/nrm
    K=(F.conj().T@F).real; ev=np.sort(np.linalg.eigvalsh(K))[::-1]
    # matched shuffle null
    n,d=F.shape; tops=[]
    for _ in range(150):
        Fs=np.empty_like(F)
        for j in range(d): Fs[:,j]=F[rng.permutation(n),j]
        Fs=Fs-Fs.mean(0,keepdims=True); nn=np.linalg.norm(Fs,axis=0,keepdims=True); nn[nn==0]=1; Fs/=nn
        tops.append(np.sort(np.linalg.eigvalsh((Fs.conj().T@Fs).real))[::-1][0])
    null=np.mean(tops)+3*np.std(tops)
    print(f"  [{label:22}] d={d:3} top eig={ev[0]:.3f}  null(mean+3σ)={null:.3f}  "
          f"-> {'REAL MODE' if ev[0]>null else 'no mode (= null)'}")
    return ev[0], null

qs3=[q for q in PRIMES if 5<q<80 and q%3==1]          # cubic symbol moduli
print("SPLIT primes only (chi_-3 support removed). Common mode vs matched null:\n")
# (P) sextic phase features: real/imag of chi(ell)*e(a_ell/q) style -> use u index phase
Fphase=np.array([[math.cos(2*math.pi*(IDX2POW[uL[l]])/6 + 2*math.pi*aL[l]/q) for q in qs3] for l in SPLIT])
corr_stats(Fphase,"sextic phase")
# (C) cubic residue symbol across q
Fcub=np.array([[math.cos(2*math.pi*(cubic_sym(l,q) or 0)/3) for q in qs3] for l in SPLIT])
corr_stats(Fcub,"cubic residue (ell/q)_3")
# (C2) cubic symbol of a_ell
Fcub2=np.array([[math.cos(2*math.pi*(cubic_sym(int(aL[l]),q) or 0)/3) for q in qs3] for l in SPLIT])
corr_stats(Fcub2,"cubic residue (a_ell/q)_3")
# (S) Sym^2: a_{ell^2}=a_ell^2 - ell, additive char at q
Fsym=np.array([[math.cos(2*math.pi*(aL[l]**2-l)/q) for q in qs3] for l in SPLIT])
corr_stats(Fsym,"Sym2 a_{l^2} add-char")
# (S2) a_ell^2 itself broadcast residue
Fsym2=np.array([[math.cos(2*math.pi*(aL[l]**2)/q) for q in qs3] for l in SPLIT])
corr_stats(Fsym2,"a_ell^2 add-char")

print("\nControl: on ALL primes, the chi_-3 mode SHOULD reappear (a_ell=0 on inert):")
ALL=[l for l in PRIMES if l>7 and 42%l!=0][:1500]
aA={l:a_ell(l) for l in ALL}
Fall=np.array([[math.cos(2*math.pi*aA[l]/q) for q in qs3] for l in ALL])
corr_stats(Fall,"a_ell add-char ALL")

print("\nRead-out: if all SPLIT-only families show 'no mode (=null)', then mu_3/mu_6")
print("are equidistributed PHASES, spectrally invisible at every order -> only mu_2")
print("(chi_-3, from supersingular vanishing) is ever real. => Thread IV theorem.")
