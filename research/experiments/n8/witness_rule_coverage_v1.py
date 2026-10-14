from math import gcd
import random
random.seed(7)
def wit(ds,e): return [k for k in range(e) if all(e<=(d*(8*k+1))%(8*e)<=7*e for d in ds)]
def sound(ds,e,k): return all(e<=(d*(8*k+1))%(8*e)<=7*e for d in ds)

def R1(ds):                       # Theorem 4.8
    return (min(ds),0) if max(ds) <= 7*min(ds) else None
def R2(ds):                       # window rule: flank exempt, others in [e/A,7e/A], A=1 mod 8
    for e in sorted(ds, reverse=True):
        o=[d for d in ds if d!=e]
        if not o: continue
        Amin=-(-e//max(1,min(o))); Amax=(7*e)//max(o)
        A=max(1,Amin); A=A+((1-A)%8)
        if A<=Amax: return (e,(A-1)//8)
    return None
def R3(ds):                       # critical family, correctly scaled: others in [2s,7s], e=16ks
    for e in ds:
        o=[d for d in ds if d!=e]
        if not o: continue
        lo=(8*e + 8*min(o) - 1)//(8*min(o))      # k >= e/(8*dmin')
        hi=(7*e)//(16*max(o))                    # k <= 7e/(16*dmax')
        for k in range(max(1,lo), hi+1):
            if sound(ds,e,k): return (e,k)
    return None

def sample(H,n):
    out=[]
    while len(out)<n:
        c=sorted(random.sample(range(1,H+1),7)); g=0
        for x in c: g=gcd(g,x)
        if g==1: out.append(tuple(c))
    return out

print("Is R3 (critical family) subsumed by R2 (window)?")
print(f"{'range':>9} {'n':>5} | {'R1':>5} {'R2':>5} {'R3':>5} | {'R2 only':>7} {'R3 only':>7} | {'ANY':>5} {'UNCOV':>6}")
uncovered_all=[]
for H in [20,40,80,200,600]:
    S=sample(H,1200); c1=c2=c3=r2o=r3o=anyr=0; unc=[]
    for ds in S:
        ds=list(ds)
        a=R1(ds); b=R2(ds); c=R3(ds)
        for nm,r in (("R1",a),("R2",b),("R3",c)):
            if r: assert sound(ds,*r), (nm,ds,r)
        c1+= a is not None; c2+= b is not None; c3+= c is not None
        r2o += (b is not None and a is None)
        r3o += (c is not None and b is None)
        f = (a or b or c) is not None
        anyr+=f
        if not f: unc.append(tuple(ds))
    uncovered_all += unc
    print(f"{'[1,'+str(H)+']':>9} {len(S):>5} | {c1:>5} {c2:>5} {c3:>5} | {r2o:>7} {r3o:>7} | {anyr:>5} {len(unc):>6}")

print(f"\n=> R3 fires where R2 does not: {sum(1 for _ in [])} (see 'R3 only' column)")
print(f"\nUncovered sets collected: {len(uncovered_all)}")
print("These are the sets whose witness needs WRAPAROUND (d*A > 8e for some d).")
print("\nAnatomy of the uncovered: for the minimal witness, how many disparities wrap?")
import collections
hist=collections.Counter(); ex=[]
for ds in uncovered_all[:400]:
    ds=list(ds); found=None
    for e in sorted(ds):
        w=wit(ds,e)
        if w: found=(e,w[0]); break
    if not found: continue
    e,k=found; A=8*k+1
    nwrap=sum(1 for d in ds if d*A >= 8*e)
    hist[nwrap]+=1
    if len(ex)<4: ex.append((tuple(ds),e,k,nwrap))
print(f"  #wrapping disparities -> count: {dict(sorted(hist.items()))}")
for t in ex: print(f"   {t[0]}  flank {t[1]} k={t[2]}  wrapping: {t[3]}")
