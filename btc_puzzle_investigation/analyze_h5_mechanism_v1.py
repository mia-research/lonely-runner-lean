#!/usr/bin/env python3
# analyze_h5_mechanism_v1.py -- nail the subgroup-confinement mechanism (run under sage for group structure).
from sage.all import *
import json, math
from collections import defaultdict

recs=[json.loads(l) for l in open("h5_followup_results_v1.jsonl")]
idx=defaultdict(list)
for r in recs: idx[(r["arm"],r["p"],r["V"])].append(r)
Ps=sorted({r["p"] for r in recs})
def logmean(qs): return math.log(sum(qs)/len(qs))

print("Group structure: j0 (A=0,B=1) vs its nearest-#E control, per prime")
print("%-5s | %-16s %-8s | %-16s %-8s | %-8s"%("p","j0 invariants","j0 cof","ctrl invariants","ctrl cof","T1_V6"))
j0_noncyc=ctrl_cyc=0
rows=[]
for p in Ps:
    F=GF(p)
    ej0=EllipticCurve(F,[0,1]); inv0=ej0.abelian_group().invariants()
    cof0 = inv0[0] if len(inv0)==1 else inv0[0]  # smaller invariant = torsion cofactor for non-cyclic
    n2_0 = inv0[0] if len(inv0)>1 else 1          # the small factor (1 if cyclic)
    ct=[r for r in idx[("baseline",p,6)] if r.get("is_ctrl")][0]
    ect=EllipticCurve(F,[ct["A"],ct["B"]]); invc=ect.abelian_group().invariants()
    n2_c = invc[0] if len(invc)>1 else 1
    j0rec=[r for r in idx[("baseline",p,6)] if r["lab"]=="j0"][0]
    t1=logmean(j0rec["quos"])-logmean(ct["quos"])
    if len(inv0)>1: j0_noncyc+=1
    if len(invc)==1: ctrl_cyc+=1
    rows.append((n2_0,t1))
    print("%-5d | %-16s %-8s | %-16s %-8s | %.4f"%(p,inv0,n2_0,invc,n2_c,t1))
print()
print("j0 non-cyclic: %d/%d ; controls cyclic: %d/%d"%(j0_noncyc,len(Ps),ctrl_cyc,len(Ps)))

# correlate T1 (|V|=6) with j0's small invariant n2 (subgroup index proxy)
import statistics
xs=[math.log(r[0]) for r in rows]; ys=[r[1] for r in rows]
mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
sxy=sum((x-mx)*(y-my) for x,y in zip(xs,ys)); sxx=sum((x-mx)**2 for x in xs); syy=sum((y-my)**2 for y in ys)
r=sxy/math.sqrt(sxx*syy) if sxx and syy else float('nan')
print("Pearson( T1_j0(|V|=6), log(n2 of j0) ) = %.3f   (n2 = size of the non-cyclic small factor; larger => more subgroup confinement)"%r)

# also: does E_F1 track the random-B twists' non-cyclicity?
print()
print("E_F1 twist cyclicity (|V|=6): are random-B j=0 twists that are MORE non-cyclic the ones with higher quo?")
allpairs=[]
for p in Ps:
    for r in idx[("F1",p,6)]:
        F=GF(p); inv=EllipticCurve(F,[0,r["B"]]).abelian_group().invariants()
        n2=inv[0] if len(inv)>1 else 1
        allpairs.append((math.log(n2), logmean(r["quos"])))
mx=sum(a for a,_ in allpairs)/len(allpairs); my=sum(b for _,b in allpairs)/len(allpairs)
sxy=sum((a-mx)*(b-my) for a,b in allpairs); sxx=sum((a-mx)**2 for a,_ in allpairs); syy=sum((b-my)**2 for _,b in allpairs)
r2=sxy/math.sqrt(sxx*syy) if sxx and syy else float('nan')
print("Pearson( logmean(quo) , log(n2) ) over all random-B j=0 twists = %.3f  (n=%d)"%(r2,len(allpairs)))
