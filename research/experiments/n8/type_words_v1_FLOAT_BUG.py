# E282 status types along the whole cascade, 7-subsets of {1..N}, gcd 1, exact Fractions, move limit 200.
# Word per set = sequence over moves of (status tuple in rank order, setter rank). Counts distinct words
# versus N, against rank words (setter ranks only) and status-only words.
import sys
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
from functools import reduce
HALF=F(1,2)
def status(d,t):
    P=8*d*t; n=floor(P+HALF); e=P-n; r=n%8
    if r==0: return 'Z'          # r0, captured
    if r==1: return 'o' if e>=0 else 'L'   # r1-: just inside leaving edge
    if r==7: return 'o' if e<=0 else 'E'   # r7+: just past entering edge
    return 'o'
def blocked(d,t):
    f=d*t-floor(d*t); return f<F(1,8) or f>F(7,8)
def nxt(d,t):
    j=floor(d*t+F(1,8)); return (8*j+1)/(8*d)
def run(ds,limit=200):
    m=ds[0]; t=F(1,8*m); word=[]; ranks=[]
    for _ in range(limit):
        st=''.join(status(d,t) for d in ds)
        bl=[i for i,d in enumerate(ds) if blocked(d,t)]
        # consistency F1: blocked <=> status != 'o'
        assert set(bl)==set(i for i,c in enumerate(st) if c!='o'), (ds,t)
        if not bl: return word,ranks,st,True
        i=max(bl,key=lambda i:nxt(ds[i],t)); word.append((st,i)); ranks.append(i); t=nxt(ds[i],t)
    return word,ranks,None,False
def main(N):
    W=set();R=set();S=set();cnt=0;fail=0;mx=0
    for c in combinations(range(1,N+1),7):
        if reduce(gcd,c)!=1: continue
        cnt+=1
        w,r,_,ok=run(c)
        if not ok: fail+=1; continue
        W.add(tuple(w)); R.add(tuple(r)); S.add(tuple(s for s,_ in w)); mx=max(mx,len(w))
    print(f"N={N} sets={cnt} unfinished={fail} maxmoves={mx} typewords={len(W)} statuswords={len(S)} rankwords={len(R)}",flush=True)
if __name__=="__main__":
    for N in map(int,sys.argv[1:]): main(N)
