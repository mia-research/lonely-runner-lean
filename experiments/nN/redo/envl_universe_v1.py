# random arrangements (NOT the tree): check chain inequality rho_{7-k} > 7(7/9)^k for >=k+1 moves with distinct first k+1 setters; and the involvement-free counter-case for >=2 moves
import sys, random, math
seed=int(sys.argv[1]); W=float(sys.argv[2]); N=int(sys.argv[3]); random.seed(seed)
def blocks(R,r):
    p=(R*r)%8; return min(p,8-p)<1-1e-9
def path(rh):
    R=1/rh[0]; st=[]
    while True:
        bl=[i for i,r in enumerate(rh) if blocks(R,r)]
        if not bl: return st,R
        ex=[((8*round(R*rh[i]/8)+1)/rh[i],i) for i in bl]
        R2,s=max(ex); st.append(s); R=R2
        if len(st)>200: return st,R
cnt={'m>=1':0,'m>=2':0,'m>=3':0,'m>=4':0,'m>=5':0,'m>=6':0}
viol={k:0 for k in range(6)}; vrep={k:0 for k in range(6)}; nrep={k:0 for k in range(6)}
mins={k:1e9 for k in range(6)}   # min of rank 7-k reading over samples with >=k+1 moves and distinct first k+1 setters
minall={k:1e9 for k in range(6)} # same without distinctness
low5_m2=0
for _ in range(N):
    top=7+(W-7)*random.random()
    mode=random.random()
    if mode<0.4: mid=[random.uniform(1,top) for _ in range(5)]
    elif mode<0.8: mid=[math.exp(random.uniform(0,math.log(top))) for _ in range(5)]
    else: mid=[random.uniform(top*0.5,top) for _ in range(5)]
    rh=sorted([1.0]+mid+[top]); 
    st,R=path(rh); m=len(st)
    if m>=2 and rh[4]<343/81-1e-9: low5_m2+=1
    for k in range(6):
        if m>=k+1:
            b=7*(7/9)**k; v=rh[6-k]
            minall[k]=min(minall[k],v)
            if len(set(st[:k+1]))==k+1:
                mins[k]=min(mins[k],v)
                if v<=b-1e-12: viol[k]+=1
            else:
                nrep[k]+=1
                if v<=b-1e-12: vrep[k]+=1
print('seed',seed,'W',W,'N',N)
print('samples with >=2 moves and rho_5 < 343/81:',low5_m2)
for k in range(6):
    print(f'k={k} rank {7-k} bound {7*(7/9)**k:.5f}: min over distinct-setter samples {mins[k]:.5f}, violations {viol[k]}; repeated-setter samples {nrep[k]}, below bound {vrep[k]}; min ignoring distinctness {minall[k]:.5f}')
