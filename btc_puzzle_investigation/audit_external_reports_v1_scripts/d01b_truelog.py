import sympy as sp
# True formal group logarithm of y^2 = x^3 + B via standard Weierstrass recursion.
# z=-x/y, w=-1/y, w = z^3 + a1 z w + a2 z^2 w + a3 w^2 + a4 z w^2 + a6 w^3 ; here only a6=B:
# w = z^3 + B w^3.  Solve as power series w(z).
z,B = sp.symbols('z B')
w = sp.Function('w')
# iterate w = z^3 + B w^3
W = sp.Integer(0)
for _ in range(8):
    W = sp.expand(z**3 + B*W**3)
    W = sp.series(W, z, 0, 30).removeO()
# x = z/w, y=-1/w ; invariant differential omega = dx/(2y) expanded in z: omega = (1 + c1 z^6 + ...) dz? 
x = sp.series(z/W, z, 0, 28).removeO()
y = sp.series(-1/W, z, 0, 28).removeO()
omega = sp.series(sp.diff(x,z)/(2*y), z, 0, 26).removeO()
omega = sp.expand(omega)
logL = sp.integrate(omega, z)
logL = sp.series(logL, z, 0, 26).removeO()
print("True invariant differential omega (in z):")
print(sp.nsimplify(omega))
print("\nTrue formal log L(z):")
print(sp.collect(sp.expand(logL), z))
# extract coeff of z^7 and z^13
print("\ncoeff z^7 :", sp.simplify(logL.coeff(z,7)), "   (doc claims 3B)")
print("coeff z^13:", sp.simplify(logL.coeff(z,13)), "   (doc claims 40 B^2)")
print("coeff z^1 :", sp.simplify(logL.coeff(z,1)))
