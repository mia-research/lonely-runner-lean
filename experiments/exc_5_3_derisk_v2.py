import math
from fractions import Fraction as F
def frac(x): return x-math.floor(x)

# For each c-branch, collect ALL good (X,Y) over a few families and characterize.
def analyze(i,j):
    print(f"\n===== ({i},{j}) =====")
    bybranch={}
    for q in range(30,80):
        for p in range(1,q):
            if math.gcd(p,q)!=1 or not(3*p<q): continue
            for r in range(q+1,(3*q)//2+1):
                if 2*r>=3*q: continue
                val=j*r-i*p
                if val%q: continue
                c=val//q
                gr=math.gcd(r,q)
                # collect ALL good l
                goods=[]
                for l in range(q):
                    t=F(2*l+1,2*q); X=frac(r*t); Y=frac(p*t)
                    if F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3):
                        # n such that 3X-5Y = c/2 + n
                        n=3*X-5*Y-F(c,2)
                        goods.append((X,Y,n))
                if goods:
                    b=bybranch.setdefault(c,{'gr':set(),'Xwin':[F(1),F(0)],'slopes':set(),'samples':[]})
                    b['gr'].add(gr)
                    for (X,Y,n) in goods:
                        b['Xwin'][0]=min(b['Xwin'][0],X); b['Xwin'][1]=max(b['Xwin'][1],X)
                        b['slopes'].add(n)
                    if len(b['samples'])<3:
                        b['samples'].append((q,p,r,c,gr,goods[0]))
    for c in sorted(bybranch):
        b=bybranch[c]
        print(f" c={c}: gcd(r,q)set={sorted(b['gr'])}, X in [{b['Xwin'][0]}, {b['Xwin'][1]}]")
        print(f"     n-values(=3X-5Y-c/2): {sorted(b['slopes'])}")
        for s in b['samples']:
            q,p,r,c,gr,(X,Y,n)=s
            print(f"     q={q},p={p},r={r}: X={X}({float(X):.3f}) Y={Y}({float(Y):.3f}) n={n}")
analyze(5,3)
analyze(5,-3)
