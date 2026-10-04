import pickle
from collections import Counter
res={}
for J in (1,2,3):
    T=pickle.load(open('terminals7_J%d.pkl'%J,'rb'))
    S={ (m,lap):{'A':set(),'B':set()} for m in (0,1,2,3,4) for lap in (True,False)}
    for p,lo,hi,rng,w,kind in T:
        w_='B' if lo>7 else 'A'
        for m in (0,1,2,3,4):
            keep=[z for z in p if z[0] <= 7-m and z[0]!=1]      # drop the top m readings and reading 1
            S[(m,True)][w_].add(tuple(keep)); S[(m,False)][w_].add(tuple(z[0] for z in keep))
    res[J]=S; del T
print("distinct chains after dropping the top m readings (and reading 1); A = landing <= 7, B = past the gate")
for lap in (True,False):
    print("with laps:" if lap else "ranks only (no laps):")
    for m in (0,1,2,3,4):
        a=[len(res[J][(m,lap)]['A']) for J in (1,2,3)]; b=[len(res[J][(m,lap)]['B']) for J in (1,2,3)]
        print(f"  top {m} dropped: A {a[0]:>7,} {a[1]:>9,} {a[2]:>9,} | B {b[0]:>6,} {b[1]:>6,} {b[2]:>6,}   (J = 1, 2, 3)")
