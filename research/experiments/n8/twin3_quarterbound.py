"""twin3_quarterbound.py -- tests the premise of the suggested union-bound route:
"the twin's kill set really has measure at most 1/4".

|A(e',J)| = (kappa*q' + s) / (8q' + rho'),  s = #{ j in J : j < rho' }.
Also computes the exact measure of the TRUE twin kill set
   K = union over base windows W_V of ( W_V  intersect  A(e', J_V) ),
and reports max |K| over q' in the stated range, per (rho0, rho').
"""
from fractions import Fraction as F
from twin3_core import A_intervals, J_set, subtract, merge, total
from twin3_window import _BW

def A_measure_formula(q, rho, J):
    kap=len(J); s=sum(1 for j in J if j<rho)
    return F(kap*q+s, 8*q+rho)

def A_measure_direct(c, J):
    return total(A_intervals(c,J))

# formula check
ok=True
for rho in range(1,8):
    for q in range(1,40):
        c=8*q+rho
        for J in [frozenset(),frozenset({0}),frozenset({3}),frozenset({0,1}),
                  frozenset({3,4}),frozenset({7,0}),frozenset({5,6})]:
            if A_measure_formula(q,rho,J)!=A_measure_direct(c,J): ok=False
print("closed form for |A(e',J)| verified:", ok)

print("\nmax |A(e',J_V)| over occurring (rho0, rho', window V), q' = 1..2000:")
worst=(F(0),None)
for rho0 in (2,4,6):
    for rho2 in (1,3,5,7,rho0):
        for a,b,V in _BW[rho0]:
            J=J_set(rho2,V)
            if not J: continue
            for q in range(1,2001):
                mu=A_measure_formula(q,rho2,J)
                if mu>worst[0]: worst=(mu,(rho0,rho2,q,8*q+rho2,sorted(V),sorted(J)))
print("   max =",worst[0],"=",float(worst[0]),"at (rho0,rho',q',e',V,J) =",worst[1])
print("   exceeds 1/4:", worst[0]>F(1,4))

print("\nexact measure of the true twin kill set K, max over q'=1..300:")
for rho0 in (2,4,6):
    for rho2 in (1,3,5,7,rho0):
        best=(F(0),None)
        for q in range(1,301):
            c=8*q+rho2
            K=[]
            for a,b,V in _BW[rho0]:
                J=J_set(rho2,V)
                if not J: continue
                K += [(max(a,u),min(b,v)) for u,v in A_intervals(c,J) if u<b and v>a]
            mk=total(merge([(u,v) for u,v in K if u<v]))
            if mk>best[0]: best=(mk,q,c)
        S=sum(b-a for a,b,V in _BW[rho0])
        print(f"   rho0={rho0} rho'={rho2}: max|K| = {best[0]} = {float(best[0]):.4f} "
              f"at q'={best[1]} (e'={best[2]});  |S|={S};  |S|-|K|-1/4 = "
              f"{S-best[0]-F(1,4)} = {float(S-best[0]-F(1,4)):.4f}")
