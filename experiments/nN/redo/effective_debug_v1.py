import sys, random
sys.argv=[sys.argv[0]]
exec(open('effective_crossings_v1.py').read().split('\nif __name__ ==')[0])
def explain(name, base, movers, qvals, s0):
    p=list(base); q=[F(0)]*7
    for m,v in zip(movers,qvals): q[m]=v
    pred, steps = predicted_next(p,q,s0); obs,a,b = observed_next(p,q,s0)
    print("="*90); print(name,"movers",movers,"s0=%.5f"%float(s0),"pred",None if pred is None else (float(pred[0]),pred[2]),"observed",obs)
    if obs is None: return
    s=F(round(obs*1e12),10**12)
    for ss in (s-F(1,10**7), s+F(1,10**7)):
        rho=rho_at(p,q,ss); st,Re=path(rho)
        print("  s=%.8f rho %s"%(float(ss),[round(float(x),4) for x in rho]))
        print("      path:",[(m['setter'],m['lap'],"R=%.5f"%float(m['R']),"blockers %s"%m['blockers']) for m in st],"landing %.5f"%float(Re))
    pr=crossings(p,q,movers)
    print("  crossings at the observed s:",[(e1,e2) for x,e1,e2 in pr if abs(x-obs)<1e-8][:8])
