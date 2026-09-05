B=7
QT.<T>=QQ[]
def Lpoly_from(poly):   # coerce any 1-var poly to QT in T
    return QT([poly[i] for i in range(poly.degree()+1)])
def newpart(p):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); aE=p+1-E.order()
    LE=1-aE*T+p*T^2
    # C_x: y^2 = w^6 + B  (genus 2)
    Hx=HyperellipticCurve(PolynomialRing(Fp,'w').0^6+B)
    Lx=Lpoly_from(Hx.frobenius_polynomial().reverse())
    # C_y: w^4 = x^3 + B (genus 3): zeta numerator
    P2.<X,Y,Z>=ProjectiveSpace(Fp,2)
    Cy=Curve(Y^4-X^3*Z-B*Z^4)
    try:
        Ly=Lpoly_from(Cy.zeta_function().numerator())
    except Exception:
        Ly=None
    return aE,LE,Hx.genus(),Lx,(Cy.geometric_genus() if Ly is None else None),Ly
def cm_disc(quad):   # for a weight-1 factor q*T^2 - c*T + 1 (or reversed): report trace & disc
    c=quad.list()
    return c
for p in [13,43,61,67,79,103,127,139]:
    if p%3!=1 or B%p==0: continue
    aE,LE,gx,Lx,gy,Ly=newpart(p)
    nx,rx=Lx.quo_rem(LE)
    print("p=%-3d a_E=%-4d | C_x g=%d  new_x=L_Cx/L_E=%s (rem %s)"%(p,aE,gx,nx.list(),rx.list()))
    if Ly is not None:
        ny,ry=Ly.quo_rem(LE)
        print("        C_y g=3  new_y=L_Cy/L_E=%s (rem %s)"%(ny.list(),ry.list()))
        print("        new_y factors:", [ (f.list(),m) for f,m in ny.factor()])
