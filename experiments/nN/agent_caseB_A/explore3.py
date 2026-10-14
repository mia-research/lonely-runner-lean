from core import *
from collections import Counter
rows=[l.split() for l in open('fine_shapes.txt')]
S=[(tuple(map(int,r[:7])),r[7]) for r in rows]
for tag in ['unif','log','late']:
    c=Counter(); lv=Counter(); first=Counter()
    for ns,t in S:
        if t!=tag: continue
        L=landing(ns); 
        c['none' if L is None else ('R<=7' if L[0]<=7 else 'R>=9')]+=1
        if L: first[(L[1],L[2])]+=1
        ll=least_level(ns); lv[ll[0] if ll else None]+=1
    print(tag, dict(c), sorted(lv.items(), key=lambda t:(t[0] is None, t[0])))
    print("  landing blocks", first.most_common(12))
lates=[ns for ns,t in S if t=='late']
mn=[min(ns[i] for ns in lates) for i in range(7)]; mx=[max(ns[i] for ns in lates) for i in range(7)]
print("late box (x/2520):", [(round(a/2520,4),round(b/2520,4)) for a,b in zip(mn,mx)])
W=Counter()
for ns in lates:
    for R,e,K in candidates(ns):
        if block_ok(ns,e,K): W[(e,K)]+=1
print("late working blocks", W.most_common(20))
