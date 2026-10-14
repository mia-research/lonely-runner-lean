# Which ingredient of the n=3/n=4 termination proofs fails at n=8?
#   (a) the NEAREST runner a stays in its first clear window: tau = a*t in [1/n, (n-1)/n]
#   (b) the return lemma Q(n-2) < 2P+1 -- stronger at n=8 than at n=4
#   (c) pigeonhole over setters: 3 at n=4, 7 at n=8
from fractions import Fraction as F
import random
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def run(n, ds, maxsteps=500):
    a = min(ds); t = F(1,n)/a; setters=[]; taus=[F(1,n)]
    for _ in range(maxsteps):
        iw=[d for d in ds if circ(d*t) < F(1,n)]
        if not iw: return setters, taus, True
        best=None
        for d in iw:
            N=round(d*t); nxt=(F(N)+F(1,n))/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d)
        if best is None: return setters, taus, False
        t=best[0]; setters.append(best[1]); taus.append(a*t)
    return setters, taus, False

for n, k, V in ((4,3,40), (8,7,40)):
    rng=random.Random(n*101)
    moves=[]; maxtau=[]; stay=0; tot=0; distinct=[]; returns=0
    for _ in range(4000):
        ds=[F(x) for x in sorted(rng.sample(range(1,V), k))]
        s,taus,arr = run(n, ds)
        if not arr: continue
        tot+=1; moves.append(len(s)); maxtau.append(max(taus))
        # (a) did the NEAREST stay inside its FIRST clear window the whole way?
        if all(t <= F(n-1,n) for t in taus): stay+=1
        distinct.append(len(set(s)))
        if len(s)!=len(set(s)): returns+=1
    moves.sort(); maxtau.sort()
    print(f"n={n}, {k} differences, {tot} arriving cascades")
    print(f"   moves            : med {moves[len(moves)//2]}  90th {moves[int(.9*len(moves))]}  max {moves[-1]}")
    print(f"   max tau = a*t    : med {float(maxtau[len(maxtau)//2]):.3f}  max {float(maxtau[-1]):.3f}"
          f"   (first window ends at {float(F(n-1,n)):.3f})")
    print(f"   (a) NEAREST stayed in its first clear window : {stay}/{tot} = {stay/tot:.3f}")
    print(f"   (c) distinct setters used  : max {max(distinct)} of {k};  cascades with a REPEAT setter: {returns}/{tot}")
    print()
