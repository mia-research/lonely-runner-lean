import random as pyr
_ns = dict(globals()); _ns["__name__"]="h"
exec(open("semaev_elimination_v1.py").read(), _ns); globals().update({k:v for k,v in _ns.items() if not k.startswith("__")})
exec(open("semaev_symmetric_reduction_lastfall_v1.py").read().split("def main()")[0], globals())
F=GF(307); A=0;B=7; E=EllipticCurve(F,[A,B]); G=E.gens()[0]; N=int(E.order())
rng=pyr.Random(1)
pts=[int(rng.randrange(1,N))*G for _ in range(6)]; Vx=[int(P[0]) for P in pts]
T=-(pts[0]+pts[1]+pts[2]); tau=int(T[0])
P,Rer,ok,S4tau,Rx=build_reduction(F,A,B,tau)
print("reduction_correct:",ok,"| P support:",len(P.monomials()),"| P total deg:",int(P.total_degree()))
r=remainder_eqs(Rer,Vx); print("remainder eqs degs:",[int(e.total_degree()) for e in r])
# planted must satisfy reduced system
pe=sym_of([F(v) for v in [Vx[0],Vx[1],Vx[2]]])
print("P(planted)=",P(pe[0],pe[1],pe[2]),"(want 0) ; r_i(planted)=",[ri(pe[0],pe[1],pe[2]) for ri in r],"(want 0s)")
