import sys; sys.path.insert(0,'.')
from envl_common_v1 import *
import collections
J=int(sys.argv[1]); T,M=load(J)
if len(sys.argv)>3: M=M[int(sys.argv[2])::int(sys.argv[3])]
c=collections.Counter(); tot=0
ex=collections.defaultdict(list)
q=F(7,9)
for idx,rh in M:
    steps,Rf=path(rh); m=len(steps); tot+=1
    Rk=[F(1)]+[s['R2'] for s in steps]
    set_=[s['setter'] for s in steps]; lap=[s['lap'] for s in steps]
    # C0 strictly increasing
    if any(Rk[i]>=Rk[i+1] for i in range(m)): c['C0 R not increasing']+=1
    # C2 step ratio
    for k in range(m):
        if not Rk[k+1] < Rk[k]*F(8*lap[k]+1,8*lap[k]-1): c['C2 ratio']+=1; break
    # C3 R_k < (9/7)^k
    for k in range(m+1):
        if not Rk[k] < F(9,7)**k and k>0: c['C3 R_k<(9/7)^k']+=1; break
    # C4 rho_{y_k} > 7 (7/9)^k
    for k in range(m):
        if not rh[set_[k]] > 7*q**k: c['C4 rho_yk>7(7/9)^k']+=1; break
    # C5 consecutive setters differ ; C7 pair used once
    if any(set_[k]==set_[k+1] for k in range(m-1)): c['C5 consecutive setter equal']+=1
    if len(set(zip(set_,lap)))<m: c['C7 pair repeated']+=1
    # C6 chain: rank 7-k >= 7(7/9)^k when m>=k+1
    for k in range(7):
        if m>=k+1:
            dist = len(set(set_[:k+1]))==k+1
            ok = rh[6-k] > 7*q**k
            c[f'C6 k={k}: cases (m>={k+1})']+=1
            if dist: c[f'C6 k={k}: first k+1 setters distinct']+=1
            if not ok:
                c[f'C6 k={k}: violations']+=1
                if dist: c[f'C6 k={k}: violations with DISTINCT setters']+=1
                else: c[f'C6 k={k}: violations with repeated setters']+=1
    # C8 involvement
    inv=set()
    for s in steps: inv|=set(s['blockers'])
    miss=[y+1 for y in range(1,7) if y not in inv]
    if miss: c['C8 reading (rank>=2) never a blocker']+=1; c['C8 missing '+str(miss)]+=1
    c['maxRlast_x1e6']=max(c['maxRlast_x1e6'], int(Rk[m-1]*10**6)) if m else c['maxRlast_x1e6']
    # C10 first-block time t_y: rho_y > 7 (7/9)^t_y  (t_y = first state index at which y is a blocker)
    first={}
    for k,sp in enumerate(steps):
        for y in sp['blockers']: first.setdefault(y,k)
    for y,t in first.items():
        if not rh[y] > 7*q**t: c['C10 violation']+=1; break
    # C11 pair count: m <= number of (y,l) pairs with 8l-1 < R_{m-1} rho_y
    if steps:
        npairs=sum(max(0,-((-(Rk[m-1]*rh[y]+1)//8))-0) for y in range(1,7))  # count of l>=1 with 8l-1 < R rho
        npairs=0
        for y in range(1,7):
            l=1
            while 8*l-1 < Rk[m-1]*rh[y]: npairs+=1; l+=1
        if m>npairs: c['C11 violation']+=1
    # C12 upper side: m>=2 with rho_2 > (8j-1) where all readings share the first zone
    if m>=2 and J==1 and rh[1]>7: c['C12 m>=2 with rho_2>7 (J1)']+=1
    if m>=2 and J==2 and rh[1]>15: c['C12 m>=2 with rho_2>15 (J2)']+=1
    # C9 smallest involved reading > 7/R_last_blocked
    if steps:
        Rl=Rk[m-1]; low=min(rh[y] for y in inv)
        if not low > 7/Rl: c['C9 violation']+=1
print('J',J,'members',tot)
for k in sorted(c): print(f'  {k}: {c[k]}')
