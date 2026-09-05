# SCOPE the Miller primitive: can Sage (a) give the reduced divisor of a Jac element,
# (b) extract the function of a principal divisor, (c) evaluate a function at a deg-3 place?
p=43; B=7
Fp=GF(p); Kf.<x>=FunctionField(Fp); Rr.<T>=Kf[]
L.<w>=Kf.extension(T^4-(x^3+B)); J=L.jacobian(model='hess'); G0=J.group()
fin=[pl for pl in L.places(1) if not pl.is_infinite_place()]
U=G0.point(fin[0].divisor()-fin[1].divisor())
V=G0.point(fin[2].divisor()-fin[3].divisor())
W=U+V
print("elt API (divisor/function-ish):", [m for m in dir(U) if any(k in m.lower() for k in ('divisor','function','repr','red'))])
# (a) reduced divisor of an element?
try:
    DW=W.divisor() if hasattr(W,'divisor') else None
    print("(a) W.divisor() ->", type(DW).__name__ if DW is not None else "no .divisor()")
except Exception as e: print("(a) err", type(e).__name__, str(e)[:60])
# (b) principal divisor -> function
DU=fin[0].divisor()-fin[1].divisor()
print("divisor API:", [m for m in dir(DU) if any(k in m.lower() for k in ('princip','function','basis','riemann'))])
try:
    Dtest=(fin[0].divisor()-fin[1].divisor())  # is this principal? generally NOT; just test the API
    print("(b) is_principal:", Dtest.is_principal() if hasattr(Dtest,'is_principal') else "no method")
except Exception as e: print("(b) err", type(e).__name__, str(e)[:60])
# (c) a deg-3 place and evaluating a function there
try:
    p3=[pl for pl in L.places(3)][:1]
    print("(c) deg-3 places found:", len(p3), "| eval x at it:", x.evaluate(p3[0]) if p3 else "none")
except Exception as e: print("(c) err (places(3) may be slow/large)", type(e).__name__, str(e)[:60])
