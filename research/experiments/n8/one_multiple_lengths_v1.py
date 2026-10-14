# For later cell ends in the dominant class: cell length (touch vs positive), blocked or clear, pass or fail, and consecutive failures.
import sys
from fractions import Fraction as F
from itertools import combinations
from one_multiple_cells_v1 import cells, disp
def opener(D,u):
    for d in D:
        v=8*d*u-1
        if v.denominator==1 and v>=0 and v%8==0: return d,int(v)//8
def main(k,N,Cmax):
    nonmult=[d for d in range(1,N+1) if d%8]
    t={'touch':{'clear':0,'blocked pass':0,'blocked fail':0},'positive':{'clear':0,'blocked pass':0,'blocked fail':0}}
    chain={}
    for D in combinations(nonmult,k):
        C=cells(D)
        if len(C)<2: continue
        u0,w0=C[0]
        for c in range(1,Cmax+1):
            x=8*c; mm=min(min(D),x)
            if disp(x,u0)<=w0: continue
            if not ((8*mm*u0).denominator==1 and x*u0==int(x*u0)): continue
            nfail=0; allpos=True
            for i in range(1,len(C)):
                u,w=C[i]; d,j=opener(D,u); r=(c*(8*j+1))%d
                kind='touch' if w==u else 'positive'
                blocked=not(d<=8*r<=7*d)
                ok=disp(x,u)<=w
                if not blocked: t[kind]['clear']+=1
                elif ok: t[kind]['blocked pass']+=1
                else: t[kind]['blocked fail']+=1
                if ok: break
                nfail+=1
            chain[nfail]=chain.get(nfail,0)+1
    print(f"k={k} N={N} C={Cmax}: by cell kind {t}; number of consecutive failing ends before the survivor: {dict(sorted(chain.items()))}",flush=True)
for a in [(4,20,12),(5,18,8),(6,16,8),(4,40,12)]: main(*a)
