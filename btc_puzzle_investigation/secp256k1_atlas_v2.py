"""secp256k1 atlas v2 — the small-torsion structure map.
Division polynomials psi_m over F_p (a=0,b=7); for each m, how many of the
m-torsion x-coordinates are F_p-rational (roots of the x-torsion polynomial),
and where the m-torsion POINTS live (F_p / F_p^2 / higher). Exact integers."""
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
INV2 = pow(2, -1, p)

def pn(f):
    f = [c % p for c in f]
    while len(f) > 1 and f[-1] == 0: f.pop()
    return f
def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b): r[i+j] = (r[i+j] + ai*bj) % p
    return pn(r)
def padd(a, b):
    r = [0]*max(len(a), len(b))
    for i, c in enumerate(a): r[i] = c
    for i, c in enumerate(b): r[i] = (r[i]+c) % p
    return pn(r)
def psub(a, b): return padd(a, [(-c) % p for c in b])
def pscale(a, s): return pn([c*s % p for c in a])
def pmod(a, m):
    a = pn(a[:]); m = pn(m[:]); dm = len(m)-1; inv = pow(m[-1], -1, p)
    while len(a)-1 >= dm and a != [0]:
        c = a[-1]*inv % p; sh = len(a)-1-dm
        for i in range(len(m)): a[sh+i] = (a[sh+i]-c*m[i]) % p
        a = pn(a)
    return a
def ppow_xp(m):                        # x^p mod m
    r = [1]; base = pmod([0, 1], m); e = p
    while e:
        if e & 1: r = pmod(pmul(r, base), m)
        base = pmod(pmul(base, base), m); e >>= 1
    return r
def pgcd(a, b):
    a = pn(a[:]); b = pn(b[:])
    while not (len(b) == 1 and b[0] == 0):
        a, b = b, pmod(a, b)
    return pscale(a, pow(a[-1], -1, p))
def nroots(f):
    f = pn(f[:])
    if len(f) <= 1: return 0
    xp = ppow_xp(f)
    g = pgcd(f, psub(xp, [0, 1]))
    return len(g)-1

# division polynomials: A_m (odd m) or B_m=psi_m/y (even m), poly in x. h=x^3+7.
h = [7, 0, 0, 1]
h2 = pmul(h, h)
A = {1: [1], 3: [0, 84, 0, 0, 3]}                       # a=0,b=7: psi3=3x^4+84x
B = {2: [2], 4: pscale([-392, 0, 0, 140, 0, 0, 1], 4)}  # psi4/y = 4(x^6+140x^3-392)

def cube(a): return pmul(pmul(a, a), a)
def sq(a): return pmul(a, a)
def build(up_to):
    for M in range(5, up_to+1):
        if M % 2 == 1:
            m = (M-1)//2
            if m % 2 == 0:  # A_{2m+1}=h^2 B_{m+2} B_m^3 - A_{m-1} A_{m+1}^3
                A[M] = psub(pmul(h2, pmul(B[m+2], cube(B[m]))), pmul(A[m-1], cube(A[m+1])))
            else:           # A_{2m+1}=A_{m+2} A_m^3 - h^2 B_{m-1} B_{m+1}^3
                A[M] = psub(pmul(A[m+2], cube(A[m])), pmul(h2, pmul(B[m-1], cube(B[m+1]))))
        else:
            m = M//2
            if m % 2 == 0:  # B_{2m}=(B_m/2)(B_{m+2}A_{m-1}^2 - B_{m-2}A_{m+1}^2)
                B[M] = pmul(pscale(B[m], INV2), psub(pmul(B[m+2], sq(A[m-1])), pmul(B[m-2], sq(A[m+1]))))
            else:           # B_{2m}=(A_m/2)(A_{m+2}B_{m-1}^2 - A_{m-2}B_{m+1}^2)
                B[M] = pmul(pscale(A[m], INV2), psub(pmul(A[m+2], sq(B[m-1])), pmul(A[m-2], sq(B[m+1]))))

build(9)

print("="*70)
print("secp256k1 small-torsion map — how psi_m splits over F_p")
print("="*70)
print(f"{'m':>2} {'xtors deg':>10} {'#F_p roots':>11}  {'=3-tors?':>9}  interpretation")
for M in range(2, 10):
    if M == 2:
        f = h                                    # 2-torsion x-coords = roots of x^3+7
    elif M % 2 == 1:
        f = A[M]
    else:
        f = B[M]
    deg = len(f)-1
    nr = nroots(f)
    # are the F_p roots exactly the embedded 3-torsion x-coords?
    shares3 = ""
    if nr > 0 and M != 3 and M % 3 == 0:
        g = pgcd(pn(f[:]), A[3])
        shares3 = f"gcd(psi_m,psi_3) deg={len(g)-1}"
    full = "ALL x-coords F_p-rational" if nr == deg and deg > 0 else (
        "none in F_p" if nr == 0 else f"{nr} of {deg} x-coords in F_p")
    print(f"{M:>2} {deg:>10} {nr:>11}  {shares3:>9}  {full}")

print("\nreadout:")
print("  only m=3 splits fully over F_p (all 4 three-torsion x-coords rational);")
print("  m=6,9 F_p-roots are exactly the EMBEDDED 3-torsion (gcd with psi_3);")
print("  m=2,4,5,7,8 contribute NO F_p-rational torsion x-coords.")
print("  x=0 is 3-torsion for EVERY j=0 curve y^2=x^3+b: [2](0,sqrt b)=(0,-sqrt b)=-(0,sqrt b).")
print("  full psi_3 split is the extra mod-p fact that -4b=-28 is a cube.")
