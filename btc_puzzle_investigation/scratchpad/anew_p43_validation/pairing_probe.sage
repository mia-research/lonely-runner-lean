p=43; B=7
Fp=GF(p); Kf.<x>=FunctionField(Fp); Rr.<T>=Kf[]
L.<w>=Kf.extension(T^4-(x^3+B)); J=L.jacobian(model='hess'); G0=J.group()
# get a nonzero element via a degree-0 divisor
fin=[pl for pl in L.places(1) if not pl.is_infinite_place()]
elt=G0.point(fin[0].divisor()-fin[1].divisor())
print("elt type:", type(elt).__name__)
print("elt methods w/ 'pair':", [m for m in dir(elt) if 'pair' in m.lower()])
print("G0 methods w/ pair/order:", [m for m in dir(G0) if 'pair' in m.lower() or m.lower()=='order'])
print("Jac methods w/ pair:", [m for m in dir(J) if 'pair' in m.lower()])
print("L (funcfield) w/ zeta/L_poly/pair:", [m for m in dir(L) if 'zeta' in m.lower() or 'l_poly' in m.lower() or 'pair' in m.lower()])
# does the function field give the zeta/L-polynomial cheaply? (would give |Jac(C)| structure)
try:
    import signal
    def h(s,f): raise TimeoutError()
    signal.signal(signal.SIGALRM,h); signal.alarm(30)
    Lp = L.L_polynomial() if hasattr(L,'L_polynomial') else None
    signal.alarm(0)
    print("L_polynomial:", Lp)
except Exception as e:
    print("L_polynomial: unavailable/slow:", type(e).__name__)
