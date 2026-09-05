# Localize the p>=499 hang step-by-step (each sub-step alarm-bounded), SKIPPING S.order()
# (R1 never needs the order). If the hang was .order(), the Jac arithmetic scales and R1 is cheap.
import signal, time
class TO(Exception): pass
def _to(s,f): raise TO()
signal.signal(signal.SIGALRM, _to)
def step(label, fn, budget=60):
    signal.alarm(budget); t=time.time()
    try:
        r=fn(); signal.alarm(0)
        print("    %-16s %.2fs" % (label, time.time()-t), flush=True); return r
    except TO:
        signal.alarm(0); print("    %-16s HANG (>%ds)" % (label, budget), flush=True); return "HANG"
    except Exception as ex:
        signal.alarm(0); print("    %-16s ERR %s %s" % (label, type(ex).__name__, str(ex)[:60]), flush=True); return "ERR"

def diag(p):
    print("p=%d  |A_new|=%d" % (p, p*p+p+1), flush=True)
    Fp=GF(p); B=7
    Kf.<x>=FunctionField(Fp); Rr.<T>=Kf[]
    st={}
    def s_setup():
        L=Kf.extension(T^4-(x^3+B)); J=L.jacobian(model='hess'); G0=J.group()
        st['L']=L; st['G0']=G0; return True
    if step("setup(L,Jac)", s_setup)=="HANG": return
    L=st['L']; G0=st['G0']; w=L.gen()
    E=EllipticCurve(Fp,[0,B]); G=E.gens()[0]; nE=Integer(G.order())
    beta=next(c for c in Fp if c!=1 and c^3==1); b2=beta^2
    def s_places():
        fin=[pl for pl in L.places(1) if not pl.is_infinite_place()]
        st['coord']={(Fp(x.evaluate(pl)),Fp(w.evaluate(pl))):pl for pl in fin}; st['npl']=len(fin); return True
    if step("places(1)", s_places, budget=90)=="HANG": return
    print("      (%d finite places)" % st['npl'], flush=True)
    coord=st['coord']
    def lift(P):
        if P.is_zero(): return None
        xP,yP=Fp(P[0]),Fp(P[1])
        if not yP.is_square(): return None
        r=yP.sqrt(); a=coord.get((xP,r)); b=coord.get((xP,-r))
        return None if (a is None or b is None) else G0.point(a.divisor()-b.divisor())
    phi=lambda P:E(beta*P[0],P[1]); phi2=lambda P:E(b2*P[0],P[1])
    d0=next(d for d in range(1,nE) if Fp((d*G)[1]).is_square())
    P0=d0*G
    Q=[None,None,None]
    def s_lift0(): Q[0]=lift(P0); return True
    if step("one .point()", s_lift0)=="HANG": return
    def s_lift12(): Q[1]=lift(phi(P0)); Q[2]=lift(phi2(P0)); return True
    if step("two more lifts", s_lift12)=="HANG": return
    def s_add():
        st['S']=Q[0]+Integer(b2)*Q[1]+Integer(beta)*Q[2]; return True
    if step("isotypic add", s_add)=="HANG": return
    S=st['S']; anew=p*p+p+1
    step("scalarmult //3", lambda: Integer(anew//3)*S)
    print("    -> Jac ARITHMETIC OK at p=%d (order() skipped)" % p, flush=True)

for p in [499, 691, 1009, 2011, 3011]:
    diag(p); print(flush=True)
