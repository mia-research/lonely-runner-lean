import math
from fractions import Fraction as F

# Pair (i,j). Relation: q | (j*r - i*p).  c defined by j*r - i*p = c*q.
# Cone/box constraints in exc_open: 0<p, 3p<q, q<r, 2r<3q, gcd(p,q)=1.
# Good time R: X={r(l+1/2)/q} in [1/6,1/2] AND Y={p(l+1/2)/q} in [1/6,1/3].

def frac(x): return x - math.floor(x)

def analyze(i,j,qmax=200):
    print(f"\n===== pair ({i},{j}) =====")
    # group survivors / witnesses by c
    cstats={}
    for q in range(18,qmax+1):
        for p in range(1,q):
            if math.gcd(p,q)!=1: continue
            if not (3*p<q): continue
            for r in range(q+1, (3*q)//2 + 1):
                if 2*r>=3*q: continue
                val = j*r - i*p
                if val % q !=0: continue
                c = val//q
                # find a good half-integer time
                found=None
                for l in range(0,q):
                    t=F(2*l+1,2*q)
                    X=frac(r*t); Y=frac(p*t)
                    if F(1,6)<=X<=F(1,2) and F(1,6)<=Y<=F(1,3):
                        found=(l,X,Y); break
                key=c
                cstats.setdefault(key,{'n':0,'wit':0,'nowit_examples':[]})
                cstats[key]['n']+=1
                if found: cstats[key]['wit']+=1
                else:
                    if len(cstats[key]['nowit_examples'])<8:
                        cstats[key]['nowit_examples'].append((q,p,r))
    for c in sorted(cstats):
        s=cstats[c]
        print(f" c={c}: {s['n']} families, {s['wit']} have R-witness, {s['n']-s['wit']} NO witness")
        if s['nowit_examples']:
            print(f"     no-witness examples (q,p,r): {s['nowit_examples']}")

analyze(5,3)
analyze(5,-3)
