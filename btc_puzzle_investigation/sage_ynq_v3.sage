FR0.<xR,yR,xQ,yQ,B> = QQ[]
FF=FR0.fraction_field()
xRf,yRf,xQf,yQf,Bf=[FF(g) for g in FR0.gens()]
lp=(yQf-yRf)/(xQf-xRf); lm=(-yQf-yRf)/(xQf-xRf)
xRpQ=lp^2-xRf-xQf; xRmQ=lm^2-xRf-xQf
yRpQ=lp*(xRf-xRpQ)-yRf; yRmQ=lm*(xRf-xRmQ)-yRf
prod=(yRpQ*yRmQ)
num=prod.numerator(); den=prod.denominator()
# map to QQ[u,v,B] with u=xQ, v=xR, substituting even y-powers
S.<u,v,Bb>=QQ[]
def toS(poly):
    poly=FR0(poly)
    res=S(0)
    for mono,coef in poly.dict().items():
        exR,eyR,exQ,eyQ,eB=mono
        if eyR%2 or eyQ%2:   # odd y-power shouldn't occur (even function); skip if any
            # substitute one y^1 pair? shouldn't happen
            raise Exception('odd y power %s'%str(mono))
        term=S(coef)*u^exQ*v^exR*Bb^eB
        term*= (u^3+Bb)^(eyQ//2) * (v^3+Bb)^(eyR//2)
        res+=term
    return res
N=toS(num); D=toS(den)
g=gcd(N,D); N//=g; D//=g
print("y_{R+Q} y_{R-Q}  as function of u=x_Q, v=x_R:")
print("  numerator  =",factor(N))
print("  denominator=",factor(D))
print("  deg_u num =",N.degree(u)," deg_u den=",D.degree(u))
