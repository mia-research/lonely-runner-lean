# Is  e2 = e1^2 - chi*p  EQUIVALENT to the 120-law (roots form two zeta3-pairs)?
# Take L*(T)=T^4 - e1 T^3 + e2 T^2 - chi*p*e1 T + p^2 with e3,e4 forced; check g=deg gcd(L*(T),L*(z3 T)).
z3 = CC(exp(2*pi*I/3))
def gdeg(p, chi, e1, e2):
    R.<T>=CC[]
    L = T^4 - e1*T^3 + e2*T^2 - chi*p*e1*T + p^2
    Lz = L(z3*T)
    g = L.gcd(Lz)
    return g.degree()
# test at sample (p, chi, e1) with e2 = e1^2 - chi*p  vs  perturbed e2
import random
print("test: does e2 = e1^2 - chi*p give g=2, and perturbed e2 give g!=2?")
for (p,chi) in [(43,-1),(67,-1),(13,1),(61,1)]:
    # pick a plausible e1 (imaginary if chi=-1, real if chi=1), |roots|=sqrt p enforced only if relation holds
    for trial in range(3):
        if chi==-1: e1 = CC(0, random.uniform(-3,3))
        else: e1 = CC(random.uniform(-3,3),0)
        e2good = e1^2 - chi*p
        e2bad  = e2good + CC(0.7)
        gg = gdeg(p,chi,e1,e2good); gb = gdeg(p,chi,e1,e2bad)
        print("  p=%d chi=%+d e1=%.2f%+.2fi :  g(relation)=%d   g(perturbed)=%d"%(p,chi,e1.real(),e1.imag(),gg,gb))
# Also: with the relation, are the roots ON |z|=sqrt(p) (purity) automatically, given real e1 magnitude?
print("\npurity under the relation (roots modulus / sqrt p), sample:")
for (p,chi,e1v) in [(43,-1,CC(0,-3.497)),(67,-1,CC(0,-2.720)),(13,1,CC(0.5,0))]:
    R.<T>=CC[]
    e2=e1v^2-chi*p
    L=T^4-e1v*T^3+e2*T^2-chi*p*e1v*T+p^2
    rts=[abs(r)/sqrt(p) for r,_ in L.roots()]
    print("  p=%d e1=%.2f%+.2fi : root moduli/sqrtp = %s"%(p,e1v.real(),e1v.imag(),[round(float(x),3) for x in rts]))
