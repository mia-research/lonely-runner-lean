from sage.all import *
import sys
sys.stdout.reconfigure(line_buffering=True)
from math import log2

# MAP the information content of the D1 transfer, instead of grading it.
# Q1: is the (n+1)/2 collapse intrinsic to psi, or imposed by the "up to sign" convention?
# Q2: what is the ceiling for ANY quotient-type map on this curve?

p = 43
E = EllipticCurve(GF(p), [0, 7])
n = E.order(); G = E.gens()[0]
K = FunctionField(GF(p), 'x'); x = K.gen()
R = PolynomialRing(K, 'T'); T = R.gen()
L = K.extension(T**4 - (x**3 + 7), 'w'); w = L.gen()
O_L = L.maximal_order()

def get_place(x0, v):
    return O_L.ideal(x - K(x0), w - L(v)).divisor().support()[0]

def get_psi(P):
    if P.is_zero():
        p0 = L.places_finite()[0]; return p0.divisor() - p0.divisor()
    x0, y0 = P.xy()
    v = y0.sqrt() if y0.is_square() else (-y0).sqrt()
    return get_place(x0, v).divisor() - get_place(x0, -v).divisor()

def equiv(D1, D2):
    D = D1 - D2
    if D.degree() != 0: return False
    try: return D.dimension() > 0
    except Exception:
        try: return len(D.basis_function_space()) > 0
        except Exception: return False

def equiv_pm(D1, D2):
    return equiv(D1, D2) or equiv(D1, -D2)

print("E: y^2=x^3+7 / F_%d   n=#E=%d   p mod 3 = %d (mu6 acts iff 1)" % (p, n, p % 3))
D_map = {d: get_psi(d * G) for d in range(n)}

def image_size(rel):
    reps = []
    for d in range(n):
        if not any(rel(D_map[d], r) for r in reps):
            reps.append(D_map[d])
    return len(reps)

I_plain = image_size(equiv)
I_pm = image_size(equiv_pm)
print("\n[Q1] psi image size")
print("  under plain linear equivalence : %d / %d   -> bits gained = %.3f" % (I_plain, n, log2(n / I_plain)))
print("  under equivalence up to sign   : %d / %d   -> bits gained = %.3f" % (I_pm, n, log2(n / I_pm)))
print("  (if plain == n, the +-collapse is the CONVENTION, not the map)")

# Q2: the ceiling. E has PRIME order -> no proper subgroups -> the only fibres a
# quotient map can have come from the automorphism group Aut(E)=mu6 acting on points.
print("\n[Q2] ceiling for quotient-type maps on this curve")
pts = [P for P in E.points() if not P.is_zero()]
# mu2 = negation ; mu3 = GLV (x -> beta x) ; mu6 = <both>
Fp = GF(p)
beta = [b for b in Fp if b != 1 and b**3 == 1]
beta = beta[0] if beta else None
def orbit_count(maps):
    seen = set(); c = 0
    for P in pts:
        if P in seen: continue
        c += 1
        stack = [P]
        while stack:
            Q = stack.pop()
            if Q in seen: continue
            seen.add(Q)
            for m in maps: stack.append(m(Q))
    return c
neg = lambda P: -P
glv = (lambda P: E(beta * P.xy()[0], P.xy()[1])) if beta is not None else None
o2 = orbit_count([neg])
o3 = orbit_count([glv]) if glv else None
o6 = orbit_count([neg, glv]) if glv else None
for name, o in (("mu2 (negation)", o2), ("mu3 (GLV)", o3), ("mu6 (Aut)", o6)):
    if o is None: continue
    img = o + 1  # + identity class
    print("  quotient by %-16s -> image %2d / %d   bits gained = %.3f" % (name, img, n, log2(n / img)))
print("  asymptotic ceiling (large n): log2|Aut(E)| = log2 6 = %.3f bits" % log2(6))
print("\n  NOTE: n prime => E has NO proper subgroups => the only group-theoretic")
print("  fibres available are Aut(E)=mu6 orbits. Maps that do NOT factor through an")
print("  Aut-quotient are OUTSIDE this ceiling and are not measured here.")
