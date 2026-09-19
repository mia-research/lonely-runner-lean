"""Does 'mean active blocker count < 1.5' preclude total blockade?
We already HAVE total blockades on file. Measure their mean blocker count directly.
If a known-shadowed configuration has mean blockers below 1.5, the sub-density argument is
refuted by an example already in the record."""
from math import gcd, lcm
from functools import reduce
def inWay(d,A,e):
    M=8*e; r=(d*A)%M; return min(r,M-r)<e
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8

print("(A) the largest-flank counterexample: ds=[-4,1,3,4,5,7,8], e=8 -- KNOWN TOTAL BLOCKADE")
ds=[-4,1,3,4,5,7,8]; e=8
qs=[e//gcd(abs(d),e) for d in ds]; Lp=reduce(lcm,qs)
tot=0; blocked_all=True; counts=[]
for k in range(Lp):
    A=8*k+1
    c=sum(1 for d in ds if inWay(d,A,e))
    counts.append(c)
    if c==0: blocked_all=False
print(f"    openings: {Lp};  every opening blocked: {blocked_all}")
print(f"    MEAN active blockers per opening: {sum(counts)/len(counts):.4f}")
print(f"    min {min(counts)}, max {max(counts)}, distribution {sorted(set(counts))}")
print()
print("(B) the extremal shadowed flanks of (2,3,4,5,6,7,16)")
def flank_stats(dsl,e):
    qs=[e//gcd(abs(d),e) for d in dsl if d!=0]; Lp=reduce(lcm,qs)
    cs=[sum(1 for d in dsl if d!=e and inWay(d,8*k+1,e)) for k in range(Lp)]
    return Lp, sum(cs)/len(cs), min(cs)
for e in (2,3,4,5,6,7,16):
    dsl=[2,3,4,5,6,7,16]
    Lp,mean,mn = flank_stats(dsl,e)
    print(f"    e={e:3d}: openings={Lp:3d}  mean blockers={mean:.4f}  min={mn}  "
          f"{'SHADOWED' if mn>0 else 'clear'}")
print()
print("(C) so: is 'mean < 1.5' compatible with total blockade?")
shad=[(e,flank_stats([2,3,4,5,6,7,16],e)) for e in (2,3,4,5,6,7)]
bad=[(e,s) for e,s in shad if s[2]>0 and s[1]<1.5]
print(f"    shadowed flanks with mean blocker count BELOW 1.5: {len(bad)}")
for e,s in bad: print(f"       e={e}: mean {s[1]:.4f}, min blockers {s[2]} -> every opening blocked")
