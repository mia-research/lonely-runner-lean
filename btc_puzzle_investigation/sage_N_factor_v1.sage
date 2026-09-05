# N(x,v) = x^3 v^3 + B(x^3+9x^2 v+9x v^2+v^3) - 8B^2.  Analyze its structure as poly in x.
# The two chi2-sums in Phi: over f1=N*(x-v) [deg4] and f2=(x^3+B)*N*(x-v) [deg7].
# If f1,f2 have SQUARE factors, the effective (squarefree) degree drops -> tighter Weil bound.
R.<x,v,B>=QQ[]
N = x^3*v^3 + B*(x^3+9*x^2*v+9*x*v^2+v^3) - 8*B^2
print("N(x,v) factor over Q[x,v,B]:", factor(N))
# treat as polynomial in x over Q(v,B)
S.<X>=PolynomialRing(FractionField(QQ['v','B']))
vv,BB=S.base_ring().gens()
Nx = X^3*vv^3 + BB*(X^3+9*X^2*vv+9*X*vv^2+vv^3) - 8*BB^2
print("\nN as poly in x:", Nx)
print("N discriminant in x:", factor(Nx.discriminant()))
f1 = Nx*(X-vv)
f2 = (X^3+BB)*Nx*(X-vv)
print("\nf1=N*(x-v) squarefree part degree:", f1.radical().degree(), " (full deg",f1.degree(),")")
print("f2=(x^3+B)*N*(x-v) squarefree part degree:", f2.radical().degree(), " (full deg",f2.degree(),")")
print("\ngcd(N, x^3+B):", gcd(Nx, X^3+BB))
print("gcd(N, x-v):", gcd(Nx, X-vv))
# Does N factor as (x-v)^2 * linear? or (quadratic)*(linear)?
print("N factor over Q(v,B):", Nx.factor())
