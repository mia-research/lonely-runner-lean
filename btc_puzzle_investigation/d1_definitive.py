from sage.all import *
import sys
sys.stdout.reconfigure(line_buffering=True)

p = 43
print("Setting up E and C over F_{}...".format(p))
E = EllipticCurve(GF(p), [0, 7])
n = E.order()
G = E.gens()[0]
K = FunctionField(GF(p), 'x'); x = K.gen()
R = PolynomialRing(K, 'T'); T = R.gen()
L = K.extension(T**4 - (x**3 + 7), 'w')
w = L.gen()
O_L = L.maximal_order()

def get_place(x0, v):
    I = O_L.ideal(x - K(x0), w - L(v))
    return I.divisor().support()[0]

def get_psi(P):
    if P.is_zero():
        p0 = L.places_finite()[0]
        return p0.divisor() - p0.divisor()
    x0, y0 = P.xy()
    if y0.is_square():
        v = y0.sqrt()
    else:
        v = (-y0).sqrt()
    Q1 = get_place(x0, v)
    Q2 = get_place(x0, -v)
    return Q1.divisor() - Q2.divisor()

def is_equivalent(D1, D2):
    D = D1 - D2
    if D.degree() != 0:
        return False
    try:
        return D.dimension() > 0
    except AttributeError:
        return len(D.basis_function_space()) > 0
    except:
        return False

def is_equiv_up_to_sign(D1, D2):
    if is_equivalent(D1, D2):
        return True
    if is_equivalent(D1, -D2):
        return True
    return False

print("Computing all D_d...")
D_map = {}
for d in range(n):
    P = d * G
    D_map[d] = get_psi(P)

print("\nChecking homomorphism up to sign: D_{i+j} ~ +/- (D_i + D_j)...")
is_hom = True
for i in range(1, 6):
    for j in range(1, 6):
        if not is_equiv_up_to_sign(D_map[(i+j)%n], D_map[i] + D_map[j]):
            is_hom = False
            print("  FAIL: D_{} + D_{} != +/- D_{}".format(i, j, (i+j)%n))
            break
    if not is_hom:
        break
if is_hom:
    print("  psi IS a homomorphism up to sign!")
else:
    print("  psi is NOT a homomorphism, even up to sign.")

print("\nMeasuring true image size up to sign...")
distinct_images = []
for d in range(n):
    D = D_map[d]
    found = False
    for D_old in distinct_images:
        if is_equiv_up_to_sign(D, D_old):
            found = True
            break
    if not found:
        distinct_images.append(D)

print("True Image size up to sign: {} out of {}".format(len(distinct_images), n))
if len(distinct_images) == (n+1)//2:
    print("This is exactly (n+1)/2. The map only identifies d and -d (trivial symmetry). NO LEVER.")
elif len(distinct_images) < n:
    print("PARTIAL REDUCTION DETECTED!")
else:
    print("NO REDUCTION: Image size equals n.")
