import pickle, random
from fractions import Fraction as F
from collections import Counter
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
exec(open('k6_longest_v1.py').read().split('rnd=random.Random')[0])
def template(K, ws):
    out=[]
    for a,b in ws:
        if a==1: L=('R1',)
        else: L=tuple(sorted(f"x{y+1}.{int((a*r-1)/8)}" for y,r in enumerate(K) if ((a*r-1)/8).denominator==1 and (a*r-1)/8>=1))
        if b==7: Rr=('R7',)
        else: Rr=tuple(sorted(f"e{y+1}.{int((b*r+1)/8)}" for y,r in enumerate(K) if ((b*r+1)/8).denominator==1 and (b*r+1)/8>=1))
        out.append((L,Rr,a==b))
    return tuple(out)
# crossers: J1/J2 members that cross, plus all seeds
cross=set(); non=[]
for J in (1,2):
    for i,rho in pickle.load(open('cell_members7_J%d.pkl'%J,'rb')):
        R=path(rho)[1]
        if R>7: cross.add(tuple(rho))
        elif len(non)<400000: non.append(tuple(rho))
for rho in pickle.load(open('stress_seeds_v1.pkl','rb')).keys(): cross.add(tuple(rho))
cross=list(cross); rnd=random.Random(7); rnd.shuffle(non); non=non[:len(cross)]
print("crossers",len(cross),"| non-crossers sample",len(non))
for name,S in (("gate crossers",cross),("non-crossers (equal size)",non)):
    row=[]
    for k in range(2,8):
        T=Counter(template(rho[:k],comps(rho[:k])) for rho in S)
        row.append((k,len(T)))
    print(name,": distinct templates of K_k, k = 2..7:",row)
# growth by random order for the K5 and K4 levels of the crossers
for k in (3,4,5,6):
    seen=set(); curve=[]
    order=cross[:]; rnd.shuffle(order)
    for n,rho in enumerate(order,1):
        seen.add(template(rho[:k],comps(rho[:k])))
        if n in (500,2000,5000,10000,len(order)): curve.append((n,len(seen)))
    print("crossers, K_%d templates, cumulative by random order:"%k,curve)
# rank-count vectors of the cascade path (moves by each rank before the gate)
V=Counter(); 
for rho in cross:
    st=path(list(rho))[0]; c=[0]*7
    for s in st:
        if s['R2']<=9: c[s['setter']]+=1
    V[tuple(c[1:])]+=1
print("crossers: distinct vectors (moves by readings 2..7 before the gate):",len(V),"| largest class",V.most_common(1)[0][1])
pickle.dump((len(cross),),open('levels_templates_v1.pkl','wb'))
