import numpy as np, pandas as pd
from scipy import stats
from sympy import isprime, totient
pv=pd.read_csv("puzzles_verified.csv"); sv=pv[pv.private_key.notna()].copy().sort_values("bits")
n=sv.n.values.astype(float); k=sv.k.values.astype(float); b=sv.bits.values.astype(float)
u=sv.u_position.values.astype(float); N=len(sv)
print(f"real keys: {N}")

print("\n=== (1) DRIFT: does n (or n-class) trend with puzzle number? ===")
for lab,y in [("n",n),("n even",(sv.n%2==0).astype(float)),
              ("n prime",np.array([isprime(int(x)) for x in n],float)),
              ("phi(n)/n",np.array([float(totient(int(x)))/int(x) for x in n])),
              ("n>=250",(n>=250).astype(float))]:
    r,p=stats.pearsonr(b,y); rs,ps=stats.spearmanr(b,y)
    print(f"  {lab:10s} vs puzzle#: Pearson r={r:+.3f} p={p:.3f} | Spearman={rs:+.3f} p={ps:.3f}")
# split early vs late puzzles
mid=np.median(b)
for lab,y in [("n even",(sv.n%2==0).astype(float)),("phi/n",np.array([float(totient(int(x)))/int(x) for x in n]))]:
    e,l=y[b<=mid].mean(),y[b>mid].mean(); print(f"  {lab}: early(<= {mid:.0f}bits)={e:.3f}  late={l:.3f}")

print("\n=== (2) u_position: uniform on [0,1)? (KS) ===")
D,p=stats.kstest(u,'uniform'); print(f"  KS vs U[0,1): D={D:.3f} p={p:.3f} ; mean={u.mean():.3f} (0.5) ; min={u.min():.3f} max={u.max():.3f}")
# is u biased low/high or clustered near simple fractions?
print(f"  frac u<0.5={np.mean(u<0.5):.3f} ; frac within 0.02 of {{0,1/2,1/3,2/3,1/4,3/4}}:",
      round(np.mean([min(abs(x-t) for t in [0,.5,1/3,2/3,.25,.75,1]) <0.02 for x in u]),3))

print("\n=== (3) k structure: is k/n uniform, k parity biased, k vs n? ===")
kn=k/n; D2,p2=stats.kstest(kn,'uniform'); print(f"  k/n KS vs U[0,1): D={D2:.3f} p={p2:.3f}")
print(f"  P(k even)={np.mean(k%2==0):.3f} (0.5?) ; P(k=1)={np.mean(k==1):.3f} ; P(k<n/2)={np.mean(k<n/2):.3f}")
print(f"  corr(n,k)={np.corrcoef(n,k)[0,1]:+.3f}")

print("\n=== (4) n mod m residue biases (did creator's n avoid residues?) ===")
for m in (3,4,5,6):
    obs=np.array([np.mean(n.astype(int)%m==r) for r in range(m)])
    chi,p=stats.chisquare(np.array([np.sum(n.astype(int)%m==r) for r in range(m)]))
    print(f"  n mod {m}: dist={np.round(obs,3)}  chi2 p={p:.3f}")

print("\n=== (5) coherent selection: how many of the composite-lean stats agree in direction? ===")
# already know direction; report joint via Fisher on the (correlated, so approximate) p-set
ps=[0.015,0.025,0.043,0.052,0.089]  # phi/n, prime, n>=250, even, omega
chi2=-2*np.sum(np.log(ps)); fp=stats.chi2.sf(chi2, 2*len(ps))
print(f"  Fisher-combined p (5 stats, NOTE correlated=>optimistic) = {fp:.4f}")
print("\nDONE")
