import pickle
res={}
for J in (1,2,3):
    T=pickle.load(open('terminals7_J%d.pkl'%J,'rb'))
    S={}
    for p,lo,hi,rng,w,kind in T:
        if lo>7: continue                                  # window A only
        lo2,hi2=rng[1]                                     # the box range of reading 2
        cls='rho_2 <= 9 (reading 2 inside the first strip)' if hi2<=9 else 'rho_2 can exceed 9 (scale separated from d_min)'
        for m in (0,1,2,3):
            keep=tuple(z for z in p if z[0]<=7-m and z[0]!=1)
            S.setdefault((cls,m),set()).add(keep)
    res[J]=S; del T
print("window A (landing <= 7): distinct chains with laps after dropping the top m readings, split by the box of reading 2")
for cls in ('rho_2 <= 9 (reading 2 inside the first strip)','rho_2 can exceed 9 (scale separated from d_min)'):
    print(cls)
    for m in (0,1,2,3):
        a=[len(res[J].get((cls,m),())) for J in (1,2,3)]
        print(f"   top {m} dropped: J=1 {a[0]:>8,} | J=2 {a[1]:>9,} | J=3 {a[2]:>9,}")
