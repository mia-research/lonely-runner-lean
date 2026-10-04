import pickle
from collections import Counter, defaultdict
def profile(J):
    T=pickle.load(open('terminals7_J%d.pkl'%J,'rb'))
    byrank=Counter(); openers=set(); lapr=defaultdict(lambda:[10**9,0]); nomove=0; mixed=0
    for p,lo,hi,rng,w,kind in T:
        win='A' if hi<=7+1e-9 else ('B' if lo>7 else 'M')
        if win=='M': mixed+=1
        if not p: nomove+=1; byrank[(None,win)]+=1; continue
        r,l=p[-1]; openers.add((r,l)); byrank[(r,win)]+=1
        a=lapr[(r,win)]; a[0]=min(a[0],l); a[1]=max(a[1],l)
    return len(T),byrank,openers,lapr,nomove,mixed
res={J:profile(J) for J in (1,2,3)}
print("OUTCOME CATALOGUE by region (opener = the zone whose exit is the landing = last move of the path; window A = landing <= 7, B = landing >= 9 (gate crossed), M = the region's marginal landing range straddles 7)")
print("window | regions | distinct openers (rank,lap) | (opener rank, window) classes | no-move regions | M regions")
for J,(n,br,op,lr,nm,mx) in res.items():
    print(f"J={J} (rho_7<={8*J+1}): {n:>9,} | {len(op):>3} | {len(br):>3} | {nm} | {mx}")
print("\nregions per (opener rank, window), J=1 / J=2 / J=3:")
keys=sorted(set(k for J in res for k in res[J][1]),key=lambda k:(k[0] or 0,k[1]))
for k in keys: print(f"  opener {k[0]} window {k[1]}: "+" / ".join(f"{res[J][1].get(k,0):>9,}" for J in (1,2,3)))
print("\nlap range of the opener per (rank, window) at J=3:")
for k in keys:
    if k in res[3][3]: print(f"  opener {k[0]} window {k[1]}: laps {res[3][3][k][0]}..{res[3][3][k][1]}")
