#!/usr/bin/env python3
"""
FAITHFUL reproduction of Finding 3 (vertical_zfr_replication.md) — 2026-07-11.
Self-audit: my earlier dismissal used order-6 Dirichlet chars mod q and NEVER
reproduced the finding's basic '3 vs 1 above the edge' phenomenon.  This builds
the ACTUAL construction:

  Dirichlet family (units mu_2 = {+-1}):
    moduli q prime; characters of F_q^* ; samples = rational primes p;
    a_chi(p) = chi(p)/sqrt(p) ; correlation over characters -> eig/edge.
  CM/Eisenstein family (units mu_6):
    INERT primes q (q==2 mod 3) so Z[omega]/(q) = F_{q^2} ; characters of
    F_{q^2}^* ; samples = Eisenstein primes pi=a+b*omega (split rational primes),
    reduced mod q into F_{q^2} = F_q[omega]; a_chi(pi)=chi(pi mod q)/sqrt(N pi).

Report, for EACH family: eigenvalues, iid MP edge, # above edge, AND # above a
MATCHED SHUFFLE NULL (mean+3sigma).  Goal: (1) reproduce the 3-vs-1 above the iid
edge; ONLY THEN (2) test whether it survives the matched null.  If I cannot
reproduce (1), I must retract the 'null artifact' claim as unverified.
"""
import numpy as np, math
rng=np.random.default_rng(7)

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]
P=sieve(300000)

# --- F_{q^2} = F_q[t]/(t^2+t+1), elements (a,b)=a+bt, t=omega ---
def fq2_mul(x,y,q):
    a,b=x; c,d=y
    # (a+bt)(c+dt)=ac + (ad+bc)t + bd t^2 ; t^2=-t-1
    return ((a*c - b*d)%q, (a*d+b*c - b*d)%q)
def fq2_pow(x,e,q):
    r=(1,0)
    while e:
        if e&1: r=fq2_mul(r,x,q)
        x=fq2_mul(x,x,q); e>>=1
    return r
def fq2_generator(q):
    order=q*q-1
    facs=set(); m=order; d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for a in range(0,q):
        for b in range(1,q):
            g=(a,b)
            if all(fq2_pow(g,order//f,q)!=(1,0) for f in facs): return g
def fq2_dlog(g,order,q):
    tab={}; cur=(1,0)
    for e in range(order): tab[cur]=e; cur=fq2_mul(cur,g,q)
    return tab

def eig_edge_null(F, k=6):
    F=F-F.mean(0,keepdims=True); nrm=np.linalg.norm(F,axis=0,keepdims=True); nrm[nrm==0]=1; F=F/nrm
    n,d=F.shape
    ev=np.sort(np.linalg.eigvalsh((F.conj().T@F).real))[::-1]
    edge=(1+math.sqrt(d/n))**2
    tops=[]
    for _ in range(150):
        Fs=np.empty_like(F)
        for j in range(d): Fs[:,j]=F[rng.permutation(n),j]
        Fs=Fs-Fs.mean(0,keepdims=True); nn=np.linalg.norm(Fs,axis=0,keepdims=True); nn[nn==0]=1; Fs/=nn
        tops.append(np.sort(np.linalg.eigvalsh((Fs.conj().T@Fs).real))[::-1][:k])
    tops=np.array(tops); nmean=tops.mean(0); nstd=tops.std(0)
    return ev, edge, nmean, nstd

# ---------------- Dirichlet family ----------------
def dirichlet_F(qs, samp):
    cols=[]
    for q in qs:
        # primitive root
        f=set(); m=q-1; d=2
        while d*d<=m:
            while m%d==0: f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        g=next(x for x in range(2,q) if all(pow(x,(q-1)//e,q)!=1 for e in f))
        ind={}; cur=1
        for e in range(q-1): ind[cur%q]=e; cur=cur*g%q
        for j in range(1,q-1):                     # non-principal chars
            cols.append([np.exp(2j*np.pi*j*ind[p%q]/(q-1))if p%q else 0 for p in samp])
    return np.array(cols).T

# ---------------- CM / Eisenstein family ----------------
def eisenstein_primes(nmax, count):
    """split rational primes p==1 mod3 with a generator pi=a+b*omega, N=a^2-ab+b^2=p."""
    out=[]
    for p in P:
        if p<=7 or p%3!=1: continue
        # cornacchia for a^2-ab+b^2=p
        for b in range(1,int((4*p/3)**.5)+2):
            dd=4*p-3*b*b
            if dd<0: break
            s=int(dd**.5)
            if s*s==dd and (s+b)%2==0:
                a=(s+b)//2; out.append((a,b,p)); break
        if len(out)>=count: break
    return out

def cm_F(qs, eis, kind="nonnorm"):
    """kind: 'nonnorm' = genuinely-F_{q^2} characters (NOT factoring through the
    norm; these see the sextic structure).  'norm' = the degenerate norm chars
    chi(pi)=chi'(N pi)=Dirichlet of p (the earlier BUG). 'sextic' = order-6 chars."""
    cols=[]
    for q in qs:                                    # inert primes q==2 mod3
        order=q*q-1; g=fq2_generator(q); tab=fq2_dlog(g,order,q)
        normstep=q+1                                 # norm chars: j multiple of q+1
        js=[]
        if kind=="norm":
            js=[(jj*normstep)%order for jj in range(1,q-1)]
        elif kind=="sextic":
            js=[k*(order//6) for k in (1,2,3,4,5)]   # exact order-6 characters
        else:                                        # nonnorm: j NOT multiple of q+1
            for j in range(1,order):
                if j%normstep!=0: js.append(j)
                if len(js)>= (q-1): break
        for j in js:
            if j%order==0: continue
            col=[]
            for (a,b,p) in eis:
                el=(a%q, b%q)
                if el==(0,0): col.append(0.0); continue
                col.append(np.exp(2j*np.pi*j*tab[el]/order))
            cols.append(col)
    return np.array(cols).T

samp=[p for p in P if 200<p<200+4000][:500]
eis=eisenstein_primes(300000, 500)
# MATCH #moduli between families to avoid a fewer-moduli confound: take the same
# COUNT of inert (CM) and split/other (Dirichlet) small primes.
qs_cm =[q for q in P if 10<q<200 and q%3==2][:8]    # inert
qs_dir=[q for q in P if 10<q<200 and q%3==1][:8]    # split (comparable count)

print("target (finding): Dirichlet eig/edge [1.089,0.929]->1 above; CM [1.269,1.174,1.106,1.022]->3 above\n")
for name,F in (("Dirichlet(mu2)",dirichlet_F(qs_dir,samp)),
               ("CM norm-chars(BUG)", cm_F(qs_cm,eis,"norm")),
               ("CM nonnorm(mu6)", cm_F(qs_cm,eis,"nonnorm")),
               ("CM sextic-only", cm_F(qs_cm,eis,"sextic"))):
    ev,edge,nmean,nstd=eig_edge_null(F)
    r=ev[:6]/edge
    above_edge=int((ev[:8]>edge).sum())
    thr=nmean+3*nstd
    above_null=int(sum(1 for i in range(6) if ev[i]>thr[i]))
    print(f"[{name}] d={F.shape[1]} n={F.shape[0]}  edge={edge:.3f}")
    print(f"   eig/edge top6: {'  '.join('%.3f'%x for x in r)}")
    print(f"   # above iid edge = {above_edge}   # above MATCHED null(mean+3σ) = {above_null}")
    print(f"   (null top3 = {'  '.join('%.3f'%x for x in nmean[:3])})\n")
print("VERDICT LOGIC: if CM shows >Dirichlet above the IID edge but 0 above the")
print("MATCHED null -> the '3 vs 1' is the iid-edge-being-wrong-null (my claim, now")
print("on the RIGHT construction). If CM shows modes above the MATCHED null too ->")
print("Finding 3 is REAL and my dismissal was wrong; retract it.")
