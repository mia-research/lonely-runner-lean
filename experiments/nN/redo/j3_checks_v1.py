import pickle, time
from fractions import Fraction as F
from collections import Counter
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
t0=time.time(); T=pickle.load(open('terminals7_J3.pkl','rb')); print("loaded",len(T),"regions in %.0f s"%(time.time()-t0),flush=True)
print("kinds:",dict(Counter(t[5] for t in T)))
byp={}
for t in T: byp.setdefault(t[0],[]).append(t)
print("distinct paths:",len(byp))
def inbox(rho,t): return all(lo-1e-9<=float(rho[y])<=hi+1e-9 for y,(lo,hi) in enumerate(t[3]))
X=[F(s) for s in ['1','2752864293769/970238379379','3691147638604/961559468885','4851775667488/988103849833','5240560485773/830842598345','2806730537001/400961505286','474233610200591258564537783/19451412054102649094869700']]
o=outcome(X); p=o['path']
print("X24: path of %d moves is a region path:"%len(p), p in byp, "| inside a region's reading box:", any(inbox(X,t) for t in byp.get(p,[])), "| region kinds:", [t[5] for t in byp.get(p,[]) if inbox(X,t)])
# gate crossers: how many regions of J=3 have a state above 9 on their path?  (landing range Rlo..Rhi above 7)
cross_regions=[t for t in T if t[2]>7]; print("regions whose landing range reaches above 7:",len(cross_regions),"| with the whole range above 7:",sum(1 for t in T if t[1]>7))
print("largest rho_7 upper bound over regions with Rlo > 7: %.4f"%max((t[3][6][1] for t in T if t[1]>7),default=0))
# earlier exact crossers: seeds and the tmpl catalogue's tuples must lie in a J=3 region (rho_7 <= 25)
seeds=list(pickle.load(open('stress_seeds_v1.pkl','rb')).keys())
miss=0; tested=0
import random
random.Random(3).shuffle(seeds)
for rho in seeds[:3000]:
    if rho[6]>25: continue
    tested+=1; pp=outcome(list(rho))['path']
    if not any(inbox(rho,t) for t in byp.get(pp,[])): miss+=1
print("3000 gate-crossing seeds with rho_7 <= 25:",tested,"| path found among J=3 regions and inside a region's box:",tested-miss,"| missing:",miss)
