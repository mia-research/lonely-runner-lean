"""Does the -7 opening's coverage settle, or decay to 0 as the arrangement range grows?
Coverage = fraction of subjects with at least one flank clear at c = -7."""
import random
def crit(d,e):
    M=8*e; r=(7*d)%M; return min(r,M-r)<e
random.seed(5)
print(" range      subjects   >=1 flank clear at c=-7      max<=7*min")
for hi in (10,30,100,10**3,10**4,10**5,10**6,10**8):
    ok=0; f7=0; n=30000
    for _ in range(n):
        v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
        ds=[v[j]-v[s] for j in range(8) if j!=s]
        A=[abs(d) for d in ds]
        if max(A)<=7*min(A): f7+=1
        if any(all(not crit(d,e) for d in ds) for e in sorted(set(A))): ok+=1
    print(f"  +-{hi:<9d} {n:7d}      {100*ok/n:6.2f}%                  {100*f7/n:6.2f}%")
