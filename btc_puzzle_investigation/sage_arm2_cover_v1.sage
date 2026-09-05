# The cover of chi2(f) is C_f: w^2 = f.  New part = Jac(C_f)/E.  Its dimension = #eigenvalues/2,
# and its char poly (from Sage zeta, FAST, exact) reveals the CM structure.
#   chi2(x): C_x: w^2=x -> y^2=w^6+B (genus 2)  -> new part dim 1 (2 eigenvalues) -> |V|<=2 sqrt p
#   chi2(y): C_y: w^2=y -> w^4=x^3+B (genus 3)  -> new part dim 2 (4 eigenvalues) -> ceiling 4 sqrt p
B=7
def newpart(p):
    Fp=GF(p)
    aE = p+1-EllipticCurve(Fp,[0,B]).order()   # trace of E
    R.<T>=ZZ[]
    Lp_E = 1 - aE*T + p*T^2
    out={}
    # C_x: y^2 = w^6 + B  (hyperelliptic genus 2)
    Hx=HyperellipticCurve(Fp['w'].0^6+B)
    Lx=Hx.frobenius_polynomial().reverse()      # L-poly, deg 4
    out['x']=(Hx.genus(), Lx)
    # C_y: w^4 = x^3 + B  (superelliptic genus 3) -- build as a curve and get zeta
    A2.<xx,ww>=AffineSpace(Fp,2)
    Cy=Curve(ww^4-(xx^3+B),A2).projective_closure()
    try:
        Zy=Cy.zeta_function()
        out['y']=(Cy.genus(), Zy)
    except Exception as ex:
        # fallback: count points over F_p^k, k=1..3, Newton
        cnts=[]
        for k in (1,2,3):
            Fk=GF(p**k,'g'); cnt=0
            for xv in Fk:
                r=xv^3+B
                cnt+=sum(1 for wv in Fk if wv^4==r)
            cnts.append(cnt)
        out['y']=('count',cnts)
    return aE, Lp_E, out

for p in [13,43,61,67,79,103,127]:
    if p%3!=1 or B%p==0: continue
    aE,LE,out=newpart(p)
    print("p=%d  a_E=%d  L_E=%s"%(p,aE,LE))
    gx,Lx=out['x']
    # new part of C_x = Lx / L_E
    R.<T>=ZZ[]
    q,r = Lx.quo_rem(LE)
    print("   C_x genus=%d  L_Cx=%s   new(=Lx/L_E)=%s  rem=%s"%(gx,Lx,q,r))
    if out['y'][0]=='count':
        print("   C_y point counts F_p^k:",out['y'][1])
    else:
        print("   C_y genus=%d  zeta numerator=%s"%(out['y'][0], out['y'][1].numerator()))
