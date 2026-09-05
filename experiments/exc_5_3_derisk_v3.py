import math
from fractions import Fraction as F
def frac(x): return x-math.floor(x)

def check(i,j):
    print(f"\n===== ({i},{j}) base s=2r{'-' if j>0 else '+'}3p =====")
    branch={}
    for q in range(30,90):
        for p in range(1,q):
            if math.gcd(p,q)!=1 or not(3*p<q): continue
            for r in range(q+1,(3*q)//2+1):
                if 2*r>=3*q: continue
                val=j*r-i*p
                if val%q: continue
                c=val//q
                s=(2*r-3*p) if j>0 else (2*r+3*p)
                if math.gcd(s%q,q)!=1:
                    print(f"  !! gcd(s,q)!=1 at q={q},p={p},r={r},c={c}"); continue
                # verify s relations
                assert (5*s - r) % q ==0 or (5*s + r)%q==0, (q,p,r)
                # pick l hitting A' window; just verify fold formula for all l
                ok=True
                for l in range(q):
                    t=F(2*l+1,2*q)
                    Ap=frac(s*t); X=frac(r*t); Y=frac(p*t)
                    # predicted
                    if j>0:
                        Xpred=frac(5*Ap - F(3*c,2)); Ypred=frac(3*Ap)
                    else:
                        Xpred=frac(-5*Ap - F(3*c,2)); Ypred=frac(3*Ap)
                    if X!=Xpred or Y!=Ypred:
                        ok=False; print(f"  MISMATCH q={q},p={p},r={r},c={c},l={l}: X={X} Xpred={Xpred} Y={Y} Ypred={Ypred}"); break
                if not ok: break
                # record window of A' that yields good (X,Y)
                b=branch.setdefault(c,{'lo':F(1),'hi':F(0),'n':0})
                b['n']+=1
                for l in range(q):
                    t=F(2*l+1,2*q); Ap=frac(s*t); X=frac(r*t); Y=frac(p*t)
                    if F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3):
                        b['lo']=min(b['lo'],Ap); b['hi']=max(b['hi'],Ap)
    for c in sorted(branch):
        b=branch[c]
        print(f"  c={c}: {b['n']} fam OK; good A' in [{b['lo']}({float(b['lo']):.3f}), {b['hi']}({float(b['hi']):.3f})]")
check(5,3)
check(5,-3)
