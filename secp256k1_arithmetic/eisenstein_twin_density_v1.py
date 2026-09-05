#!/usr/bin/env python3
"""
Eisenstein twin prime density  (Thread 1)  —  exact-integer, matched Bateman-Horn.

Object.  A "primary Eisenstein twin prime" is pi = a + b*omega in Z[omega] with
BOTH N(pi) and N(pi-1) prime, where N(a+b w) = a^2 - a b + b^2.  Since the
secp256k1 Frobenius satisfies pi_n = pi_p - 1, this is exactly "p and n both
prime" = a prime-order j=0 (CM by Z[omega]) curve.

Question (the only NEW checkable content of the thread):  is the joint event a
number-theoretic *rarity beyond* "n prime given p prime", or is it exactly what
Bateman-Horn predicts for the pair of quadratic forms
    F(a,b) = a^2 - a b + b^2            (= N(pi)   = p)
    G(a,b) = (a-1)^2 - (a-1) b + b^2    (= N(pi-1) = n)?

Method.  Count lattice points (a,b) in a box with F,G both prime (exact sieve),
then compare to the Bateman-Horn prediction
    E = S * sum_{(a,b) in box, F,G>=2} 1/(ln F * ln G),
    S = prod_q (1 - nu(q)/q^2)/(1 - 1/q)^2,   nu(q)=#{(a,b) mod q: F*G ==0}.
A ratio observed/E ~ 1 says the twin condition is GENERIC (fully Bateman-Horn),
i.e. secp256k1 is not special beyond being a prime-order curve.

No floating point touches any primality decision; floats appear only in the
heuristic density value E and in reported ratios (display, not signal path).
"""
import math

# ---------- exact sieve ----------
def sieve(N):
    s = bytearray([1]) * (N + 1)
    s[0] = s[1] = 0
    for i in range(2, int(N**0.5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return s

def norm(a, b):            # exact integer
    return a*a - a*b + b*b

# ---------- singular series S = prod_q (1 - nu(q)/q^2)/(1-1/q)^2 ----------
def small_primes(n):
    s = sieve(n)
    return [i for i in range(2, n+1) if s[i]]

def nu_analytic(q):
    """#{(a,b) mod q : F==0 or G==0}, F,G the shifted disc(-3) forms.
    Zeros of a^2-ab+b^2 mod q: 2q-1 if -3 is a QR (q==1 mod 3), else 1.
    Intersection reduces to 3a^2-3a+1==0 (disc -3): 2 roots if q==1 mod 3 else 0.
    q=2,3 done by hand (see derivation)."""
    if q == 2:
        return 2
    if q == 3:
        return 6
    if q % 3 == 1:
        A = 2*q - 1          # zeros of each form
        I = 2                # simultaneous zeros
        return 2*A - I       # = 4q - 4
    else:                    # q % 3 == 2 (inert)
        return 2             # A=1 each, I=0

def singular_series(qmax=200000):
    S = 1.0
    for q in small_primes(qmax):
        nu = nu_analytic(q)
        S *= (1 - nu / (q*q)) / (1 - 1/q)**2
    return S

# ---------- main count ----------
def nu_brute(q):
    nu = 0
    for a in range(q):
        for b in range(q):
            F = (a*a - a*b + b*b) % q
            G = ((a-1)*(a-1) - (a-1)*b + b*b) % q
            if F == 0 or G == 0:
                nu += 1
    return nu

def main():
    for q in small_primes(60):
        assert nu_analytic(q) == nu_brute(q), (q, nu_analytic(q), nu_brute(q))
    print("nu_analytic == nu_brute for all primes < 60  [OK]")

    BOX = 500                      # a,b in [-BOX, BOX]
    maxnorm = 3 * BOX * BOX + 5    # max of a^2-ab+b^2 on the box
    s = sieve(maxnorm)

    twin = 0
    Fprime = 0
    bh_sum = 0.0                   # sum 1/(lnF lnG) over F,G>=2 lattice pts
    # bins by norm magnitude to measure the conditional constant kappa = P(n|p)*ln(N)
    import collections
    binF = collections.Counter()
    binT = collections.Counter()
    def dec(x):
        return len(str(x))         # decimal-digit bin
    for a in range(-BOX, BOX + 1):
        for b in range(-BOX, BOX + 1):
            F = norm(a, b)
            G = norm(a - 1, b)
            if F >= 2 and G >= 2:
                bh_sum += 1.0 / (math.log(F) * math.log(G))
            if F >= 2 and s[F]:
                Fprime += 1
                binF[dec(F)] += 1
                if G >= 2 and s[G]:
                    twin += 1
                    binT[dec(F)] += 1

    S = singular_series(qmax=20000)
    E = S * bh_sum

    print(f"box: a,b in [-{BOX},{BOX}]   ({(2*BOX+1)**2} lattice points)")
    print(f"  # with F=N(pi) prime            : {Fprime}")
    print(f"  # Eisenstein twin (F & G prime) : {twin}")
    print(f"  Bateman-Horn singular series S  : {S:.6f}")
    print(f"  BH prediction  E = S * sum      : {E:.1f}")
    print(f"  observed / predicted            : {twin/E:.4f}")
    print()
    print(f"  empirical P(n prime | p prime)  : {twin/Fprime:.5f}")
    # naive 'random n ~ 1 mod 3' baseline at the box's median norm scale:
    # median norm ~ BOX^2; conditional prime density among n==1 mod 3 ~ (3/2)/ln
    med = BOX * BOX
    naive = 1.5 / math.log(med)
    print(f"  naive (3/2)/ln(median norm~{med}) : {naive:.5f}")

    print()
    print("  kappa = P(n|p)*ln(N) by norm size (should be ~scale-stable):")
    kappas = []
    for d in sorted(binF):
        if binF[d] < 200:
            continue
        Nmid = 10**(d - 0.5)
        pcond = binT[d] / binF[d]
        kappa = pcond * math.log(Nmid)
        kappas.append(kappa)
        print(f"    {d}-digit norms: nF={binF[d]:6d}  P(n|p)={pcond:.4f}  kappa={kappa:.3f}")
    kbar = sum(kappas) / len(kappas)
    print(f"  mean kappa (conditional constant) ~ {kbar:.3f}")

    # ---------- secp256k1 placement ----------
    p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
    from sympy import isprime
    print()
    print(f"  secp256k1: p prime? {isprime(p)},  n prime? {isprime(n)}")
    pcond_secp = kbar / math.log(n)
    print(f"  ln(n) = {math.log(n):.2f}")
    print(f"  extrapolated P(n prime | p prime) at secp scale = kappa/ln(n) = {pcond_secp:.5f}")
    print(f"     ( ~ 1 in {1/pcond_secp:.0f} primes p (== 1 mod 3) give a prime-order j=0 twin )")

if __name__ == "__main__":
    main()
