# Thread #4: Semaev cusp leading form + S4 all-t singular locus geometry
p = 211; F = GF(p); A = F(0); B = F(7)
def S3(a,b,c): return (a-b)^2*c^2 - 2*((a+b)*(a*b+A)+2*B)*c + ((a*b-A)^2 - 4*B*(a+b))
R.<x1,x2,x3,t,X> = PolynomialRing(F)
S4 = R(S3(x1,x2,X).resultant(S3(x3,t,X), X))

print("=== (1) leading form == cusp (y^2=x^3, A=B=0) summation poly? ===")
d = S4.degree()
top = sum(cf*mm for cf,mm in zip(S4.coefficients(),S4.monomials()) if mm.degree()==d)
def S3c(a,b,c): return (a-b)^2*c^2 - 2*((a+b)*(a*b))*c + ((a*b)^2)
S4cusp = R(S3c(x1,x2,X).resultant(S3c(x3,t,X), X))
print("  S4 leading form == S4|_{A=B=0} (cusp)? ", top == S4cusp)
print("  cusp fact: y^2=x^3 smooth locus ~ additive group G_a via (u^2,u^3); pts sum to O iff sum(u_i)=0")

print("=== (2) singular locus of the S4 fibre V_t (fixed t): where are the singular points? ===")
Rf = PolynomialRing(F, ['y1','y2','y3'], order='degrevlex')
y1,y2,y3 = Rf.gens()
import random; random.seed(int(3))
for tv in [F(random.randrange(1,p)) for _ in range(4)]:
    phi = R.hom([y1,y2,y3,tv,F(0)], Rf)
    f = phi(S4)
    grads = [f.derivative(v) for v in Rf.gens()]
    J = Rf.ideal([f]+grads)
    dJ = J.dimension()
    Joff = J + Rf.ideal([(y1-y2)*(y1-y3)*(y2-y3)])   # impose two coords equal
    dOff = Joff.dimension()
    verdict = "ON the diagonal x_i=x_j" if dOff == dJ else "has OFF-diagonal part"
    print("  t=%3d: sing dim=%d ; with prod(x_i-x_j)=0 dim=%d => singular locus %s" % (tv, dJ, dOff, verdict))
