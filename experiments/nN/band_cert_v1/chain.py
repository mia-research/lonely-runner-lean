import sys, proto, random
from proto import TS, last_ok
from fractions import Fraction as F
from core import clear_set
proto.MINW = 2.0**-int(sys.argv[4])
def ok_leaf(S,L,a,b):
    S2=TS(S,a,b)
    if not S2: return False
    return last_ok(S2,b) if L==2 else proto.cover(S2,L-1,1.0,b)
def descend(S,L,a,b,chain):
    while True:
        if b-a<proto.MINW:
            S2=TS(S,a,b); chain.append((L,a,b,S2))
            if not S2 or L==2: return chain
            return descend(S2,L-1,1.0,b,chain)
        m=(a+b)/2
        if not proto.cover(S,L,a,m): b=m
        else: a=m
S0=eval(sys.argv[3])
ch=descend(S0,6,float(sys.argv[1]),float(sys.argv[2]),[])
for c in ch: print(c[0],c[1],c[2],[(round(p,5),round(q,5)) for p,q in c[3]])
# sample exact configurations inside the chain boxes
rng=random.Random(1); best=None
boxes={c[0]:(F(c[1]),F(c[2])) for c in ch}
for t in range(3000):
    s=[F(1)]
    for L in [6,5,4,3,2]:
        a,b=boxes[L]; s.append(a+(b-a)*F(rng.randint(0,1000),1000))
    s.append(F(rng.randint(1000,int(s[-1]*1000)),1000))
    S=clear_set(s,F(1),F(40)); v=S[0][0]
    if best is None or v>best[0]: best=(v,s,S)
print("max least clear in chain boxes:",float(best[0]),[float(x) for x in best[1]])
print([(round(float(a),5),round(float(b),5)) for a,b in best[2] if b<16])
