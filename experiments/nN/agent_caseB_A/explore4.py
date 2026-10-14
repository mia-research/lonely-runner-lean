from core import *
from collections import Counter
def L2(ns):
    for i in range(1,7):
        if 9*ns[i-1] <= 7*ns[i] and 3*ns[6] <= 5*ns[i]: return i
    return None
def ok_blocks(ns, Kmax):
    return [(e,K) for R,e,K in candidates(ns) if K<=Kmax and block_ok(ns,e,K)]
rows=[l.split() for l in open('fine_shapes.txt')]
S=[tuple(map(int,r[:7])) for r in rows if r[7]!='late']
S+= list(integer_band_sets(24))
res=[ns for ns in S if L2(ns) is None]
print("residual after L2", len(res), "of", len(S))
for Kmax in [1,2,3,4,5,6,8,16]:
    unc=[ns for ns in res if not ok_blocks(ns,Kmax)]
    print("Kmax",Kmax,"uncovered",len(unc))
# after level1 all e: what fails first for (e,2) e=4,5,6
unc1=[ns for ns in res if not ok_blocks(ns,1)]
why=Counter()
for ns in unc1:
    key=[]
    for e in (4,5,6):
        ne=ns[e]; bad=[]
        for d,nd in enumerate(ns):
            r=(17*nd)%(8*ne)
            if r<ne or r>7*ne: bad.append(d)
        key.append(tuple(bad))
    why[tuple(key)]+=1
print("level-1-uncovered", len(unc1))
for k,v in why.most_common(25): print(v,k)
