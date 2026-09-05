# Factor L*(T) = T^4 - e1 T^3 + (e1^2 - chi*p) T^2 - chi*p*e1 T + p^2 with the relation imposed.
# Show it factors into two zeta3-related quadratics.
R.<e1,p,chi,z3> = QQ[]
# work in fraction field with z3^2 = -1 - z3 relation handled manually where needed
S.<T> = PolynomialRing(FractionField(R))
L = T^4 - e1*T^3 + (e1^2 - chi*p)*T^2 - chi*p*e1*T + p^2
print("L*(T) =", L)
print("\nfactor over Q(e1,p,chi):")
print(factor(L))
# Try the ansatz (T^2 + b1 T + c1)(T^2 + b2 T + c2). Solve.
var('b1 b2 c1 c2 E1 P CHI')
lhs = (T^2+b1*T+c1)*(T^2+b2*T+c2)
# match coefficients symbolically via a Groebner/solve
Rr.<b1,b2,c1,c2,E1,P,CHI>=QQ[]
eqs = [ b1+b2 - (-E1),
        c1+c2+b1*b2 - (E1^2-CHI*P),
        b1*c2+b2*c1 - (-CHI*P*E1),
        c1*c2 - P^2 ]
I = Rr.ideal(eqs)
print("\nGroebner basis of the factorization system (eliminating to find c1,c2 relations):")
GB = I.groebner_basis()
for g in GB: print("  ",g)
