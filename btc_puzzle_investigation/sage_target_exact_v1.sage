B=7
# (A) chi=-1 anti-palindromic reduction: use y = W - 1/W  (roots on circle -> y imaginary, y=2i sin th)
var('e W y')
Pm = W^4 - e*W^3 + (e^2 + 1)*W^2 + e*W + 1     # chi=-1: e^2-chi = e^2+1 ; -chi*e = +e
# divide by W^2:  (W^2+1/W^2) - e(W - 1/W) + (e^2+1) ; note W^2+1/W^2=(W-1/W)^2+2 = y^2+2
red = (y^2+2) - e*y + (e^2+1)
print("chi=-1 reduction (y=W-1/W): ", red.expand(), " = y^2 - e y + (e^2+3)")
disc = (e^2 - 4*(e^2+3)).simplify_full()
print("  disc_y = ", disc, " = -3(e^2+4) < 0  => y purely imaginary => W on unit circle for |e|<=2? check roots")
# y = 2 i sin(theta) => y^2 = -4 sin^2 <=0 real; need y roots of y^2-e y+(e^2+3). For chi=-1, e=e1/sqrt p is imaginary: e=i*u.
var('u')
redi = red.subs(e==I*u).expand()
print("  with e=i*u (u real): ", redi, "  -> y^2 - i u y + (-u^2+3)")
# roots y=(iu +- sqrt(-u^2 -4(-u^2+3)))/2 = (iu +- sqrt(3u^2-12))/2 ; real-on-circle needs W=exp(i th): y=2i sin th (imaginary)
# y imaginary <=> sqrt(3u^2-12) imaginary <=> 3u^2-12<=0 <=> |u|<=2  == |e|<=2 == CAP
print("  y imaginary (W on circle) <=> 3u^2-12<=0 <=> |u|<=2 == |e|<=2 == CAP  [chi=-1 confirmed]")

print("\n===== EXACT cyclotomic verification of  S_2 = -S_1^2 + 2*chi2(-1)*p  =====")
def verify(p, amax=None):
    Fp=GF(p); E=EllipticCurve(Fp,[0,B]); n=E.order()
    if not is_prime(n): return None
    K.<z>=CyclotomicField(n)
    G=None
    for P in E.points():
        if P.order()==n: G=P;break
    dlog={};Q=E(0)
    for d in range(n): dlog[Q]=d;Q=Q+G
    chi=1 if Fp(-1).is_square() else -1
    # k=1 data
    d1=[(1 if P[1].is_square() else -1, dlog[P]) for P in E.points() if not P.is_zero() and P[1]!=0]
    # k=2 data
    F2=GF(p^2,'g');E2=EllipticCurve(F2,[0,B]);fr=F2.frobenius_endomorphism()
    d2=[]
    for P in E2.points():
        if P.is_zero() or P[1]==0: continue
        c=1 if P[1].is_square() else -1
        T=P+E2(fr(P[0]),fr(P[1]))
        dl=0 if T.is_zero() else dlog[E(Fp(T[0]),Fp(T[1]))]
        d2.append((c,dl))
    bad=0; tot=0
    amax=amax or n
    for a in range(1,amax):
        S1=-sum(c*z^((a*dl)%n) for c,dl in d1)
        S2=-sum(c*z^((a*dl)%n) for c,dl in d2)
        if S2 != -S1^2 + 2*chi*p: bad+=1
        tot+=1
    return dict(p=p,n=n,chi=chi,bad=bad,tot=tot)
for p in [13,43,67,79,103]:
    if p%3!=1 or B%p==0: continue
    r=verify(p)
    if r: print("  p=%-3d n=%-3d chi2(-1)=%+d :  S_2 = -S_1^2 + 2*chi*p  holds at %d/%d cells (EXACT in Z[zeta_n])"
                %(r['p'],r['n'],r['chi'],r['tot']-r['bad'],r['tot']))
