import mpmath as mp
mp.mp.dps=30
exec(open("recon_exact.py").read().split("def metric")[0])  # reuse EC + E setup
def metrics(tvals):   # returns (rho_inf, rho2)
    corr=mp.mpf(0); Fhat={}
    for bc in BC:
        e=E[bc]; U=sum(tvals[i]*e[i] for i in range(n-1)); au=abs(U); corr+=au
        Fhat[bc]=(mp.conj(U)/au) if au>0 else mp.mpc(0)
    corr/=n
    Finf=mp.mpf(0); l2=mp.mpf(0)
    for i in range(n-1):
        Fd=sum(Fhat[bc]*E[bc][i] for bc in BC); a=abs(Fd)
        if a>Finf: Finf=a
        l2+=a*a
    l2=mp.sqrt(l2/(n-1))
    return (corr/Finf if Finf>0 else mp.mpf(0), corr/l2 if l2>0 else mp.mpf(0))
wn=2*mp.pi/n
lam=next(t for t in range(2,n) if pow(t,3,n)==1 and t!=1)
orbit=set((s*pow(lam,j,n))%n for s in (1,n-1) for j in range(3))
inf={}; two={}
for ap in range(1,n):
    ri,r2=metrics([mp.e**(-1j*wn*ap*d) for d in range(1,n)])
    inf[ap]=float(ri); two[ap]=float(r2)
for nm,R in [("rho_inf (sup-norm)",inf),("rho_2 (scalar)",two)]:
    ov=[R[a] for a in orbit]; oth=[R[a] for a in R if a not in orbit]
    above=sum(1 for a in R if a not in orbit and R[a]>=min(ov))
    v=sorted(R.values())
    print(f"  {nm:20}: orbit={sum(ov)/len(ov):.5f}  others mean={sum(oth)/len(oth):.5f} max={max(oth):.5f}  | non-orbit >= orbit-min: {above}/{len(oth)}  -> {'SEPARATES orbit' if above==0 else 'does NOT separate (generic)'}")
