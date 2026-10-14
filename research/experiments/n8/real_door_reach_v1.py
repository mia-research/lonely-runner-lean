"""How much of the REAL target does the window door cover?
Condition: exists i0 != k and j : N with  1/8 <= |(v i - v k) * t| <= 7/8  for all i != k,
where t = (j + 1/8)/|v i0 - v k|.  Real arrangements, no integers anywhere."""
import random
def covers(v,k,jmax=400):
    ds=[v[i]-v[k] for i in range(8) if i!=k]
    for i0 in range(8):
        if i0==k: continue
        e=abs(v[i0]-v[k])
        if e==0: continue
        for j in range(jmax):
            t=(j+0.125)/e
            if all(0.125 <= abs(d*t) <= 0.875 for d in ds): return True
    return False
random.seed(7)
print("real arrangements (uniform speeds), fraction of SUBJECTS covered by the window door:")
for lab,gen in (("uniform [0,1)", lambda: [random.random() for _ in range(8)]),
                ("uniform [0,10)", lambda: [10*random.random() for _ in range(8)]),
                ("log-uniform 1..1000", lambda: [10**(3*random.random()) for _ in range(8)])):
    hit=0; tot=0; allk=0; na=0
    for _ in range(4000):
        v=gen()
        if len(set(v))<8: continue
        na+=1
        c=sum(1 for k in range(8) if covers(v,k))
        hit+=c; tot+=8
        if c==8: allk+=1
    print(f"   {lab:22s} subjects {100*hit/tot:5.2f}%   arrangements with ALL 8 subjects: {100*allk/na:5.2f}%")
print()
print("the condition forces max|d| <= 7*min|d| (a ratio-7 spread), so:")
for lab,gen in (("uniform [0,1)", lambda: [random.random() for _ in range(8)]),
                ("log-uniform 1..1000", lambda: [10**(3*random.random()) for _ in range(8)])):
    ok=0; tot=0
    for _ in range(20000):
        v=gen(); 
        for k in range(8):
            ds=[abs(v[i]-v[k]) for i in range(8) if i!=k]
            tot+=1
            if max(ds) <= 7*min(ds): ok+=1
    print(f"   {lab:22s} subjects with ratio-7 spread: {100*ok/tot:5.2f}%")
