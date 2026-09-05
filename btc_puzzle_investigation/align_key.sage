# Serious audit of the "alignment key" leakage thesis on a ground-truth GLV curve.
# Objects: (j,s) orbit phase; carry c from GLV balanced decomp; lift norm s_lift (Eisenstein);
# boundary indicator eps. Question threaded through all: OBSERVABLE from P, or only from d?
import math
from collections import Counter
p,b,n,beta,lam = load("/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/a2e97e4b-0256-4ffa-8e2a-5d92f74d8482/scratchpad/curvedata.sobj")
F=GF(p); E=EllipticCurve(F,[0,b]); G=E.gens()[0]
lam=Integer(lam); n=Integer(n)
pts=[None]*n; cur=E(0)
for d in range(n): pts[d]=cur; cur=cur+G
def c3(v):
    v=Integer(v)%p
    if v==0: return 0
    t=power_mod(v,(p-1)//3,p); return 0 if t==1 else (1 if t==beta else 2)
def MI(feat,tgt):
    j=Counter(zip(feat,tgt)); fx=Counter(feat); fy=Counter(tgt); N=len(feat); I=0.0
    for (a,c),k in j.items(): I+=(k/N)*math.log2((k/N)/((fx[a]/N)*(fy[c]/N)))
    return I
def corr(xs,ys):
    mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
    num=sum((a-mx)*(c-my) for a,c in zip(xs,ys))
    den=math.sqrt(sum((a-mx)**2 for a in xs)*sum((c-my)**2 for c in ys))
    return num/den if den else 0.0

# --- GLV lattice L={(a,bb): a+bb*lam ≡0 mod n}, Gauss-reduced basis ~ sqrt(n) ---
def gauss_reduce(v1,v2):
    while True:
        if v1[0]**2+v1[1]**2 > v2[0]**2+v2[1]**2: v1,v2=v2,v1
        m=round((v1[0]*v2[0]+v1[1]*v2[1])/(v1[0]**2+v1[1]**2))
        if m==0: return v1,v2
        v2=(v2[0]-m*v1[0], v2[1]-m*v1[1])
v1,v2=gauss_reduce((n,0),(-lam%n,1))
import numpy as np
B=matrix(ZZ,[list(v1),list(v2)]); Binv=B.inverse()
def balanced(d):
    # (d,0) = (d1,d2) + lattice pt ; Babai round
    coef=vector(QQ,[d,0])*Binv
    rc=vector(ZZ,[round(coef[0]),round(coef[1])])
    latpt=rc*B
    d1,d2=d-latpt[0], -latpt[1]
    return Integer(d1),Integer(d2),(coef[0]-rc[0],coef[1]-rc[1])
print("GLV short basis v1=%s v2=%s  (|v|~sqrt(n)=%.0f)"%(v1,v2,float(sqrt(n))))

# --- build per-d: observables (from P) and hidden alignment quantities (from d) ---
Ndata=n-1
obs_chi3x=[]; obs_chi2y=[]; obs_Fphase=[]; obs_Fmag=[]; obs_xmod=[]
hid_c=[]; hid_d1=[]; hid_slift=[]; hid_halfplane=[]
d_list=list(range(1,n))
for d in d_list:
    x,y=map(Integer,pts[d].xy())
    obs_chi3x.append(c3(x)); obs_chi2y.append(1 if power_mod(Integer(y)%p,(p-1)//2,p)==1 else -1)
    obs_Fphase.append(c3(x)); obs_Fmag.append(1 if y>p//2 else 0)
    obs_xmod.append(x%97)
    d1,d2,frac=balanced(d)
    c=d2                                   # the lambda-carry
    slift=float(frac[0]**2 - frac[0]*frac[1] + frac[1]**2)  # Eisenstein norm of Babai residual
    hid_c.append(c); hid_d1.append(d1); hid_slift.append(slift); hid_halfplane.append(1 if d<n//2 else 0)

print("\n=== CLAIM 1: (j,s) '100%% leaked' — but does it CONSTRAIN d? ===")
print("  MI((j,s) ; d mod 3)      = %.5f bit"%MI(list(zip(obs_Fphase,obs_Fmag)),[d%3 for d in d_list]))
print("  MI((j,s) ; halfplane)    = %.5f bit"%MI(list(zip(obs_Fphase,obs_Fmag)),hid_halfplane))
print("  MI((j,s) ; carry c bucket)= %.5f bit"%MI(list(zip(obs_Fphase,obs_Fmag)),[cc%16 for cc in hid_c]))
print("  (j,s) computable from P: YES. Bits it pins about d: see above.")

print("\n=== CLAIM 2: the +-0.58 trace<->carry correlation. WHICH pair? ===")
# B1: HIDDEN trace (d-derived, e.g. d1) vs HIDDEN carry c  -- is 0.58 here & is it forced?
print("  [B1 hidden-vs-hidden] corr(d1, c)          = %.4f"%corr([float(x) for x in hid_d1],[float(x) for x in hid_c]))
print("  [B1 hidden-vs-hidden] corr(d mod3 signed, c)= %.4f"%corr([1.0 if d%3==0 else -0.5 for d in d_list],[float(x) for x in hid_c]))
# B2: OBSERVABLE trace (function of P only) vs HIDDEN carry c  -- the one that matters
print("  [B2 OBSERVABLE-vs-hidden] corr(chi2(y), c) = %.4f"%corr([float(x) for x in obs_chi2y],[float(x) for x in hid_c]))
print("  [B2 OBSERVABLE-vs-hidden] corr(chi3(x), c) = %.4f"%corr([float(x) for x in obs_chi3x],[float(x) for x in hid_c]))
print("  [B2] MI(all observables ; c bucket mod16)  = %.5f bit"%MI(list(zip(obs_chi3x,obs_chi2y,obs_Fmag,obs_xmod)),[cc%16 for cc in hid_c]))

print("\n=== CLAIM 3: eps 'perfectly leaked' inside Eisenstein inradius s_lift<3/16 ===")
thr=3/16.0
inside=[i for i in range(Ndata) if hid_slift[i]<thr]
print("  fraction of keys with s_lift<3/16 : %.3f  (n_inside=%d)"%(len(inside)/Ndata,len(inside)))
# is the SELECTION (s_lift<3/16) observable from P?
sel=[1 if hid_slift[i]<thr else 0 for i in range(Ndata)]
print("  MI(observables ; [s_lift<3/16] selection) = %.5f bit   (can you even TELL which keys are inside, from P?)"%
      MI(list(zip(obs_chi3x,obs_chi2y,obs_Fmag,obs_xmod)),sel))
# inside the disk, is eps deterministic / observable?
anchor=54321
eps=[1 if (d_list[i]+anchor>=n) else 0 for i in range(Ndata)]
eps_in=[eps[i] for i in inside]
print("  inside disk: H(eps)=%.4f bit (eps still ~random?)  mean(eps)=%.3f"%
      ((lambda c: -sum((v/len(eps_in))*math.log2(v/len(eps_in)) for v in Counter(eps_in).values()))(0), sum(eps_in)/len(eps_in)))
obs_in=[ (obs_chi3x[i],obs_chi2y[i],obs_Fmag[i]) for i in inside]
print("  inside disk: MI(observables ; eps) = %.5f bit  (is eps a free leak there?)"%MI(obs_in,eps_in))

print("\n=== POSITIVE CONTROL: harness can detect a real dependence ===")
print("  MI(d mod3 ; d mod3) = %.5f bit (=log2 3)"%MI([d%3 for d in d_list],[d%3 for d in d_list]))
print("  corr(c, c) = %.4f"%corr([float(x) for x in hid_c],[float(x) for x in hid_c]))

print("\n=== SHUFFLE CONTROLS for the two elevated MI numbers (bias vs signal) ===")
import random; random.seed(int(0))
cbuck=[cc%16 for cc in hid_c]; cbuck_sh=cbuck[:]; random.shuffle(cbuck_sh)
joint=list(zip(obs_chi3x,obs_chi2y,obs_Fmag,obs_xmod))
print("  MI(observables ; c%%16)         real=%.5f  shuffled=%.5f  -> %s"%(
    MI(joint,cbuck), MI(joint,cbuck_sh), "SIGNAL" if MI(joint,cbuck)-MI(joint,cbuck_sh)>0.02 else "bias floor"))
sel=[1 if hid_slift[i]<3/16.0 else 0 for i in range(Ndata)]; sel_sh=sel[:]; random.shuffle(sel_sh)
print("  MI(observables ; [s<3/16] sel) real=%.5f  shuffled=%.5f  -> %s"%(
    MI(joint,sel), MI(joint,sel_sh), "SIGNAL" if MI(joint,sel)-MI(joint,sel_sh)>0.005 else "bias floor"))
# also: drop the high-cardinality x%97 feature, use only algebraic chars
joint2=list(zip(obs_chi3x,obs_chi2y,obs_Fmag))
print("  MI(chars only, no x%%97 ; c%%16)  real=%.5f  shuffled=%.5f"%(MI(joint2,cbuck),MI(joint2,cbuck_sh)))
