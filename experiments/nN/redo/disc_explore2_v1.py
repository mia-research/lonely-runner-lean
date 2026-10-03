import pickle, numpy as np
from fractions import Fraction as F
from collections import Counter
recs = pickle.load(open('disc_records_v1.pkl','rb'))
# openers
op=Counter(); 
for ci,rh,R,w,ps,st,ex in recs:
    op[(ex[-1][0]+1, ex[-1][1])]+=1
print("openers (rank,lap):",sorted(op.items(), key=lambda x:-x[1])[:40])
# readings: integer?
ic=Counter()
for ci,rh,*_ in recs:
    ic[tuple(int(r.denominator==1) for r in rh)]+=1
print(ic.most_common(12))
# opener reading integer?
c=Counter(); 
for ci,rh,R,w,ps,st,ex in recs:
    y=ex[-1][0]; c[rh[y].denominator==1]+=1
print("opener reading integer:",c)
# check R* == (8j+1)/rho
bad=sum(1 for ci,rh,R,w,ps,st,ex in recs if R!=F(8*ex[-1][1]+1)/rh[ex[-1][0]]); print("opener identity fails",bad)
# R* near gap edges
Rs=sorted((r[2],r[0]) for r in recs)
import bisect
ks=[x[0] for x in Rs]
i=bisect.bisect_left(ks,F(7)); print("below 7: largest 5:",[(str(Rs[j][0]),float(Rs[j][0])) for j in range(i-5,i)])
j=bisect.bisect_left(ks,F(7)); print("above 7: smallest 5:",[(str(Rs[k][0]),float(Rs[k][0])) for k in range(j,j+5)])
print("count R*==9", sum(1 for k in ks if k==9), "R*==7",sum(1 for k in ks if k==7), "R*<9", bisect.bisect_left(ks,F(9)))
print("smallest R*:",[float(x) for x in ks[:5]],"largest",[float(x) for x in ks[-5:]])
