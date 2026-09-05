# Derive y_{R+Q} * y_{R-Q} as a rational function of x_Q, x_R for E: y^2 = x^3 + B.
var('xR yR xQ yQ B')
# slopes
lp = (yQ - yR)/(xQ - xR)     # R+Q
lm = (-yQ - yR)/(xQ - xR)    # R-Q
xRpQ = lp^2 - xR - xQ
xRmQ = lm^2 - xR - xQ
yRpQ = lp*(xR - xRpQ) - yR
yRmQ = lm*(xR - xRmQ) - yR
prod = (yRpQ*yRmQ).simplify_full()
# substitute yR^2 = xR^3+B, yQ^2 = xQ^3+B to eliminate yR,yQ (product is even in yQ and in yR)
prod2 = prod.subs(yR^2 == xR^3+B).simplify_full()
prod3 = prod2.subs(yQ^2 == xQ^3+B).simplify_full()
# It should be a rational function of xQ, xR only (no yQ,yR). Try to force:
num = prod3.numerator(); den = prod3.denominator()
print("PRODUCT y_{R+Q} y_{R-Q} (raw):")
print(prod3)
print("\n-- as (num)/(den), reduced mod yR^2=xR^3+B, yQ^2=xQ^3+B --")
# Repeated reduction
expr = prod
for _ in range(6):
    expr = expr.subs(yR^2==xR^3+B).subs(yQ^2==xQ^3+B).simplify_full()
print(expr)
