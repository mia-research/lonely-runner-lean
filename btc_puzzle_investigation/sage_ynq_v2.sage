R.<xR,yR,xQ,yQ,B> = QQ[]
I = R.ideal([yQ^2-(xQ^3+B), yR^2-(xR^3+B)])
Rq = R.quotient(I)
lpn = (yQ - yR); lpd=(xQ-xR)           # lambda_+ = lpn/lpd
lmn = (-yQ - yR)
# x_{R+Q} = lp^2 - xR - xQ ; work with common denominator lpd^2
# y_{R+Q} = lp*(xR - x_{R+Q}) - yR = lp*(2xR + xQ - lp^2) - yR
# multiply everything by lpd^3 to clear denominators, track factor
# y_{R+Q} * lpd^2 = lpn*(2xR+xQ)*lpd - lpn^3/lpd ... messy; just do rational in fraction field
FR = R.fraction_field()
xR,yR,xQ,yQ,B = FR(xR),FR(yR),FR(xQ),FR(yQ),FR(B)
lp=(yQ-yR)/(xQ-xR); lm=(-yQ-yR)/(xQ-xR)
xRpQ=lp^2-xR-xQ; xRmQ=lm^2-xR-xQ
yRpQ=lp*(xR-xRpQ)-yR; yRmQ=lm*(xR-xRmQ)-yR
prod=yRpQ*yRmQ
# reduce numerator and denominator modulo the ideal by substituting yQ^2,yR^2
def red(poly):
    # poly in R; reduce
    return R(poly).reduce(I)
num=red(prod.numerator()); den=red(prod.denominator())
print("num reduced:",num)
print("den reduced:",den)
g=gcd(num,den)
print("gcd:",g)
print("PRODUCT =",factor(num//g),"  /  ",factor(den//g))
