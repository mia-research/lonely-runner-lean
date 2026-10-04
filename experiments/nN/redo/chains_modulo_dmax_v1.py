import pickle
from collections import Counter
def variants(p):
    full=tuple(p)
    no7=tuple(z for z in p if z[0]!=7)                         # drop reading 7's moves (d_max)
    no7_1=tuple(z for z in no7 if z[0]!=1)                     # also drop reading 1's move (d_min gate)
    ranks_only=tuple(z[0] for z in no7_1)                      # keep only which reading moved, in order
    mark7=tuple(('*',) if z[0]==7 else z for z in p)           # reading 7 moves kept as a placeholder, laps of 7 forgotten
    return full,no7,no7_1,ranks_only,mark7
names=["full path","drop reading-7 moves","also drop reading 1","ranks only (middle readings, no laps)","reading 7 as placeholder (laps of 7 forgotten)"]
res={}
for J in (1,2,3):
    T=pickle.load(open('terminals7_J%d.pkl'%J,'rb'))
    sets=[{'A':set(),'B':set()} for _ in names]
    for p,lo,hi,rng,w,kind in T:
        w_='B' if lo>7 else 'A'
        for i,v in enumerate(variants(p)): sets[i][w_].add(v)
    res[J]=sets; del T
print("distinct chains by variant; window A (landing <= 7) / window B (past the gate):")
for i,n in enumerate(names):
    print(f"  {n}:")
    for J in (1,2,3): print(f"     J={J}: A {len(res[J][i]['A']):>8,} | B {len(res[J][i]['B']):>6,}")
print("\nnew chains at J=3 relative to J=2, by variant (A / B):")
for i,n in enumerate(names): print(f"  {n}: A {len(res[3][i]['A']-res[2][i]['A']):,} | B {len(res[3][i]['B']-res[2][i]['B']):,}")
