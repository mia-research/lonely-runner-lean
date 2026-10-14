"""Item 3, continued.  The middle region is 1 <= M <= c-2, M = #{d : n | d}.
Both closed ends pick their flank by a rule: M=0 takes a flank coprime to n, M>=c-1 takes the
lone non-multiple.  So: in the MIDDLE, which flank actually works?  If it is always one kind,
that is the rule to write.
"""
from itertools import combinations
import math, collections
def works(ds,e,n):
    M=n*e
    for j in range(e):
        if all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in ds): return True
    return False
for n,HI in ((5,26),(6,20),(7,15)):
    k=n-1
    tot=0; kinds=collections.Counter(); first=[]
    for c in combinations(range(1,HI+1),k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        M=sum(1 for d in c if d%n==0)
        if not (1 <= M <= len(c)-2): continue      # the middle region only
        tot+=1
        good=[e for e in c if works(c,e,n)]
        if not good: kinds["NO FLANK WORKS"]+=1; continue
        # classify every working flank
        cop = [e for e in good if math.gcd(e,n)==1]
        mult= [e for e in good if e%n==0]
        other=[e for e in good if math.gcd(e,n)>1 and e%n!=0]
        if cop and not mult and not other: kinds["only coprime flanks work"]+=1
        elif mult and not cop and not other:  kinds["only multiples of n work"]+=1
        elif other and not cop and not mult:  kinds["only partial-gcd flanks work"]+=1
        else: kinds["mixed"]+=1
        if len(first)<3: first.append((c,good,[math.gcd(e,n) for e in good]))
    print(f"n={n}  middle-region sets in [1,{HI}]: {tot}")
    for kk,v in kinds.most_common(): print(f"     {kk:<28} {v}")
    for c,g,gc in first: print(f"     e.g. ds={c}  working flanks {g}  gcd(e,n)={gc}")
    print()
