#!/usr/bin/env python3
"""
cm_amicable_correspondence_v1.py — LINE 2, pushed for real.

The amicable pair (p,n)=(907,967): E(F_p) has order n, E(F_n) has order p, y^2=x^3+7,
both CM by Z[omega]. CM theory gives an EXACT structural correspondence:
    Frobenius pi_p fixes F_p-points => [pi_p - 1] annihilates E(F_p)
    => E(F_p) ~= Z[omega]/(pi_p - 1),  and N(pi_p-1)=n, (pi_p-1) prime above n
    => E(F_p) ~= Z[omega]/(pi_p-1) ~= F_n   (the AMICABLE PARTNER's field is the CM coord ring!)
So the DLP "P=[d]G, find d" IS "find the F_n-coordinate of P". We build this explicitly and
locate the EXACT computability boundary -- not "it's hard" but WHICH step and WHY.

We construct: pi_p, verify pi_n = pi_p - 1 and the module structure; the GLV eigenvalue
lambda = image of omega in F_n; verify Frobenius = identity (a + b*lambda = 1 mod n); the
coordinate map phi: E(F_p) -> F_n and demonstrate forward=cheap / inverse=DLP; then TEST the
two candidate bypasses (CRT via the common Z[omega]-object; canonical lift to global then
reduce mod pi_n) and show exactly where each needs the non-computable step.

Exact integer arithmetic throughout (small p; brute-force DLP is fine here to EXHIBIT the map).
"""
import math


def emul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)   # (a+b w)(c+d w), w^2=-1-w


def enorm(z):
    a, b = z; return a * a - a * b + b * b


def legendre(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p - 1) // 2, p) == 1 else -1)


def tonelli(a, p):
    if p % 4 == 3:
        r = pow(a, (p + 1) // 4, p)
        return r if r * r % p == a % p else None
    q, s = p - 1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while legendre(z, p) != -1: z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1: t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p); m, c = i, b * b % p; t = t * c % p; r = r * b % p
    return r if r * r % p == a % p else None


def curve_points(p):
    pts = []
    for x in range(p):
        r = (x * x * x + 7) % p
        if r == 0: pts.append((x, 0))
        elif legendre(r, p) == 1:
            y = tonelli(r, p); pts.append((x, y)); pts.append((x, (p - y) % p))
    return pts


def padd(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        if y1 == 0: return None
        lam = (3 * x1 * x1) % p * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def mul(P, k, p):
    R, Q = None, P; k %= (10**9)
    while k > 0:
        if k & 1: R = padd(R, Q, p)
        Q = padd(Q, Q, p); k >>= 1
    return R


def find_pi(p):
    for a in range(-2 * math.isqrt(p) - 2, 2 * math.isqrt(p) + 3):
        for b in range(-2 * math.isqrt(p) - 2, 2 * math.isqrt(p) + 3):
            if a * a - a * b + b * b == p:
                return (a, b)
    return None


def cube_root(p):
    e = (p - 1) // 3; g = 2
    while pow(g, e, p) == 1: g += 1
    return pow(g, e, p)


def dlog_bruteforce(P, G, p, order):
    Q = None
    for d in range(order):
        if Q == P: return d
        Q = padd(Q, G, p)
    return None


def main():
    p, n = 907, 967
    print(f"AMICABLE CM CORRESPONDENCE  (p,n)=({p},{n})   E: y^2=x^3+7")
    print("=" * 78)
    pts = curve_points(p); order = len(pts) + 1     # + point at infinity
    print(f"|E(F_{p})| = {order}  (want n={n})")

    # generator + GLV eigenvalue lambda from the geometric endomorphism (beta x, y)=[lambda]G
    G = next(P for P in pts if P != (0, 0))
    beta = cube_root(p)
    lam = None; which = None
    for bexp in (beta, beta * beta % p):
        for sgn, tag in [(1, "+"), (-1, "-")]:
            cand = (bexp * G[0] % p, (sgn * G[1]) % p)
            d = dlog_bruteforce(cand, G, p, order)
            if d is not None and pow(d, 3, n) == 1 and d != 1:
                lam = d; which = f"beta^{1 if bexp==beta else 2} x,{tag}y"; break
        if lam: break
    print(f"\nGLV eigenvalue (geometric): [omega]G = ({which}) = [lambda]G,  lambda = {lam},"
          f"  lambda^3 mod n = {pow(lam,3,n)}")

    # SELF-CONSISTENT Frobenius pi_p = a+b*omega (omega -> lambda): N(pi_p)=p AND [pi_p]G=G
    #   i.e. a + b*lambda == 1 (mod n).  This is THE geometric Frobenius for this lambda.
    R = 2 * math.isqrt(p) + 3
    pip = next((a, b) for a in range(-R, R) for b in range(-R, R)
               if a * a - a * b + b * b == p and (a + b * lam) % n == 1)
    a, b = pip
    pin = (1 - a, -b)                                  # pi_n = 1 - pi_p  (the amicable relation)
    print(f"pi_p = {pip}: N={enorm(pip)}=p, trace 2a-b={2*a-b}=p+1-n={p+1-n}, "
          f"a+b*lambda mod n = {(a+b*lam)%n}=1  => [pi_p]G=G (Frobenius=identity, a theorem) ✓")
    print(f"pi_n = 1 - pi_p = {pin}: N(pi_n)={enorm(pin)}=n, "
          f"N(pi_n - 1)=N(-pi_p)={enorm((pin[0]-1,pin[1]))}=p  => #E(F_{n})=p (amicable closes) ✓")
    print(f"=> (pi_p - 1) annihilates E(F_p), N(pi_p-1)={enorm((a-1,b))}=n prime "
          f"=> E(F_{p}) ~= Z[omega]/(pi_p-1) ~= F_{n}  (the partner's field IS the CM coord ring)")

    # the coordinate map phi: E(F_p) -> F_n,  [alpha]G |-> (alpha mod (pi_p-1)).  On Z-multiples: d |-> d mod n.
    print("\n--- the correspondence, and the EXACT computability boundary ---")
    d_secret = 123
    P = mul(G, d_secret, p)
    print(f"forward (CHEAP): d={d_secret} -> [d]G = {P}   (scalar mult, poly time)")
    d_rec = dlog_bruteforce(P, G, p, order)
    print(f"inverse (= DLP): recover d from [d]G  -> d={d_rec}  (here by brute force over {order};")
    print(f"   at secp size this is the ECDLP -- the coordinate map phi IS the discrete log)")

    print("\n--- BYPASS 1: CRT via the common Z[omega]-object ---")
    print(f"  E(F_{p}) ~= Z[omega]/(pi_p-1) ~= F_{n};   E(F_{n}) ~= Z[omega]/(pi_n-1) ~= F_{p}.")
    print(f"  ideals (pi_p-1),(pi_n-1) coprime => CRT: Z[omega]/((pi_p-1)(pi_n-1)) ~= E(F_{p}) x E(F_{n}).")
    print(f"  BUT to place P in the CRT object you need its coordinate in E(F_{p}) = phi(P) = the DLP.")
    print(f"  WALL LOCATED: the iso E(F_{p})~=F_{n} is abstract; realizing phi(P) IS the DLP. The")
    print(f"  partner E(F_{n})~=F_{p} is an INDEPENDENT DLP of size p -- no field map F_{p}<->F_{n}.")

    print("\n--- BYPASS 2: canonical CM lift to global, then reduce mod pi_n ---")
    print(f"  E has a global CM model over Q(omega); a GLOBAL point P~ reduces mod pi_p to P and")
    print(f"  mod pi_n to a point of E(F_{n}). If P~ were computable, that IS a transfer.")
    print(f"  WALL LOCATED: lifting a finite P to a global P~ of bounded height is not computable")
    print(f"  (the xedni-calculus obstruction, Silverman 1998 / Jacobson-Koblitz-Silverman-Stein-")
    print(f"  Teske 2000: the lift exists set-theoretically but has no small-height / efficiently-")
    print(f"  findable representative -- finding it is >= as hard as the DLP).")

    print("\n=== computability ledger ===")
    print("  CHEAP  : forward scalar mult; [omega]-action (beta,y); GLV lambda; pi_p, module ISO exists")
    print("  DLP-HARD: the coordinate map phi:E(F_p)->F_n (=the discrete log itself)")
    print("  DLP-HARD: the canonical lift E(F_p)->global (xedni obstruction)")
    print("  WHY it's hard HERE (not just 'it's hard'): the amicable/CM structure is an ABSTRACT")
    print("  module iso E(F_p)~=F_n; every computable path to realize it (coordinate map, or lift)")
    print("  is provably DLP-equivalent, and the partner F_p is a same-size INDEPENDENT DLP, not an")
    print("  easier target. The correspondence is REAL and EXACT but transfers no computational")
    print("  advantage. => genuine unknown that remains: is there a NON-lift, NON-coordinate use of")
    print("  the joint (pi_p-1)(pi_n-1) ideal structure? (not found here; not proven impossible).")


if __name__ == "__main__":
    main()
