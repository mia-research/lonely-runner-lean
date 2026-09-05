#!/usr/bin/env python3
# CORRECTED-NULL follow-up to bit_readout_leak_test_v1.py.
# HYPOTHESIS: the v1 "ESCAPE" (z=5-8) is a NULL MISMATCH (master retraction #6): coordinate bits are
#   EVEN in d (x_{-d}=x_d => x&1, hi(x) satisfy F(d)=F(n-d); y&1 is complemented-even F(n-d)=1-F(d)).
#   A value-permutation null destroys that mu2 symmetry, so the concentration gap measures the symmetry,
#   not a d-leak. TEST: re-rank each readout against a SYMMETRY-MATCHED null (permute {d,n-d} orbits,
#   preserving the exact even/odd symmetry + value multiset). PREDICTION: z collapses to ~0 => artifact.
#   FALSIFICATION: z survives (>=5) against the matched null => a real leak beyond the mu2 symmetry.
import numpy as np
from sympy import isprime, nextprime

def legendre(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
def ecount(p):
    return p+1+sum(legendre((x*x%p*x+7)%p,p) for x in range(p))
def sqrt_mod(a,p):
    a%=p
    if a==0: return 0
    if pow(a,(p-1)//2,p)!=1: return None
    if p%4==3: return pow(a,(p+1)//4,p)
    q,s=p-1,0
    while q%2==0: q//=2; s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    m,c,t,r=s,pow(z,q,p),pow(a,q,p),pow(a,(q+1)//2,p)
    while t!=1:
        t2,i=t,0
        while t2!=1: t2=t2*t2%p; i+=1
        b=pow(c,1<<(m-i-1),p); m,c,t,r=i,b*b%p,t*b*b%p,r*b%p
    return r
def ec_add(P,Q,p):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    lam=(3*x1*x1)*pow(2*y1,p-2,p)%p if P==Q else (y2-y1)*pow((x2-x1)%p,p-2,p)%p
    x3=(lam*lam-x1-x2)%p
    return (x3,(lam*(x1-x3)-y1)%p)
def first_point(p):
    for x in range(p):
        y=sqrt_mod((x*x%p*x+7)%p,p)
        if y is not None: return (x,y)

def concentration(F):
    F=F.astype(np.float64); F0=F-F.mean(); rms=np.sqrt((F0*F0).mean())
    if rms==0: return 0.0
    return (np.abs(np.fft.fft(F0))/len(F))[1:].max()/rms

def matched_null_even(F, n, rng, B, kind):
    """Null preserving the d<->n-d symmetry of F. kind='even': F(n-d)=F(d); 'codd': F(n-d)=1-F(d)-like
       handled by permuting orbit-representative values and reflecting."""
    half=(n-1)//2
    reps=np.arange(1,half+1)                       # orbit reps d=1..(n-1)/2 ; partner n-d
    vals=F[reps].copy()
    out=np.empty(B)
    for b in range(B):
        perm=rng.permutation(vals)
        G=np.zeros(n)
        G[reps]=perm
        if kind=='even':
            G[n-reps]=perm                         # F(n-d)=F(d)
        else:                                      # complemented-even: F(n-d)=vmax+vmin-F(d) (parity flip)
            G[n-reps]=(vals.max()+vals.min())-perm
        out[b]=concentration(G)
    return out

def main():
    rng=np.random.default_rng(20260719)
    p=nextprime(50226)
    while not (p%6==1 and isprime(ecount(p)) and ecount(p)>=40000): p=nextprime(p)
    n=ecount(p); G=first_point(p)
    print(f"p={p} n={n} G={G}")
    x=np.zeros(n,dtype=np.int64); y=np.zeros(n,dtype=np.int64); P=None
    for d in range(1,n):
        P=ec_add(P,G,p); x[d],y[d]=P
    # verify symmetry x_{-d}=x_d exactly
    ev=np.all(x[1:]==x[n-np.arange(1,n)])
    print(f"exact x_(-d)=x_d (even): {ev}   y_(-d)=-y_d: {np.all((y[1:]+y[n-np.arange(1,n)])%p==0)}")

    readouts={"x & 1":(x&1,'even'),"hi(x)=[2x>=p]":((2*x>=p).astype(np.int64),'even'),
              "x mod 4":(x%4,'even'),"x & 15":(x&15,'even'),
              "y & 1":(y&1,'codd'),"hi(y)=[2y>=p]":((2*y>=p).astype(np.int64),'codd')}
    B=400
    print(f"\n{'readout':<14} {'C(F)':>9} {'z_plainshuf':>12} {'z_MATCHED':>11} {'rankp_M':>9}")
    print("-"*60)
    for name,(F,kind) in readouts.items():
        F=F.astype(np.int64); c=concentration(F)
        # plain value-shuffle (the v1 null)
        plain=np.array([concentration(rng.permutation(F)) for _ in range(B)])
        zp=(c-plain.mean())/(plain.std()+1e-15)
        # symmetry-matched null
        mn=matched_null_even(F,n,rng,B,kind)
        zm=(c-mn.mean())/(mn.std()+1e-15); rpm=(np.sum(mn>=c)+1)/(B+1)
        print(f"{name:<14} {c:9.5f} {zp:12.2f} {zm:11.2f} {rpm:9.4f}")
    print("\nreading: z_plainshuf high but z_MATCHED ~0  => the concentration IS the mu2 (even) symmetry,")
    print("not a d-leak (v1 ESCAPE = null mismatch, retraction #6). z_MATCHED>=5 would be a real leak.")

if __name__=="__main__":
    main()
