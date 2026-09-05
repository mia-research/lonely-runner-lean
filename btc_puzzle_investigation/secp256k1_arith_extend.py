"""Atlas thread 4 — extend the arithmetic atlas.
(a) small-factor structure of p±1, n±1 (subgroup / Pohlig-Hellman structure).
(b) embedding-degree tower ord_ℓ(p) over primes up to 100.
(c) confirm the torsion pattern (only 3-torsion x-coords F_p-rational) past m=9."""
from sympy import isprime, primerange

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def smooth(m, bound=5_000_000):
    fac = {}
    for q in [2] + list(range(3, bound, 2)):
        if q*q > m: break
        while m % q == 0: fac[q] = fac.get(q, 0)+1; m //= q
    return fac, m

print("=== (a) small-factor structure of p±1, n±1 ===")
for name, m in [("p-1", p-1), ("p+1", p+1), ("n-1", n-1), ("n+1", n+1)]:
    fac, cof = smooth(m)
    s = " · ".join(f"{q}^{e}" if e > 1 else f"{q}" for q, e in fac.items())
    print(f"  {name} = {s} · C   where C is {cof.bit_length()}-bit, prime={isprime(cof)}")
print("  (n-1 full: 2^6·3·149·631·107361793816595537·174723607534414371449·")
print("            341948486974166000522343609283189 — from thread 1)")

print("\n=== (b) embedding-degree tower  ord_ℓ(p)  for ℓ < 100 ===")
def ordp(a, l):
    o = 1; x = a % l
    if x == 0: return 0
    while x != 1: x = x*a % l; o += 1
    return o
low = []
row = []
for l in primerange(2, 100):
    k = ordp(p, l); row.append(f"{l}:{k}")
    if k <= 3: low.append((l, k))
for i in range(0, len(row), 8): print("  " + "  ".join(row[i:i+8]))
print(f"  smallest embedding degrees (ord_ℓ(p) ≤ 3): {low}")
print(f"  ⇒ ℓ with ord=1 (μ_ℓ ⊂ F_p, i.e. ℓ | p−1): {[l for l,k in low if k==1]}")

print("\n=== (c) torsion pattern past m=9 (division polynomials, #F_p roots) ===")
INV2 = pow(2, -1, p); h = [7, 0, 0, 1]
def pn(f):
    f = [c % p for c in f]
    while len(f) > 1 and f[-1] == 0: f.pop()
    return f
def pm(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b): r[i+j] = (r[i+j]+ai*bj) % p
    return pn(r)
def pa(a, b):
    r = [0]*max(len(a), len(b))
    for i, c in enumerate(a): r[i] = c
    for i, c in enumerate(b): r[i] = (r[i]+c) % p
    return pn(r)
def ps(a, b): return pa(a, [(-c) % p for c in b])
def psc(a, s): return pn([c*s % p for c in a])
def pmod(a, m):
    a = pn(a[:]); m = pn(m[:]); dm = len(m)-1; inv = pow(m[-1], -1, p)
    while len(a)-1 >= dm and a != [0]:
        c = a[-1]*inv % p; sh = len(a)-1-dm
        for i in range(len(m)): a[sh+i] = (a[sh+i]-c*m[i]) % p
        a = pn(a)
    return a
def nroots(f):
    f = pn(f[:])
    if len(f) <= 1: return 0
    r = [1]; base = pmod([0, 1], f); e = p
    while e:
        if e & 1: r = pmod(pm(r, base), f)
        base = pmod(pm(base, base), f); e >>= 1
    a, bb = pn(f[:]), ps(r, [0, 1])
    while not (len(bb) == 1 and bb[0] == 0): a, bb = bb, pmod(a, bb)
    return len(psc(a, pow(a[-1], -1, p)))-1
h2 = pm(h, h)
A = {1: [1], 3: [0, 84, 0, 0, 3]}
B = {2: [2], 4: psc([-392, 0, 0, 140, 0, 0, 1], 4)}
def cube(x): return pm(pm(x, x), x)
def sq(x): return pm(x, x)
for M in range(5, 14):
    if M % 2:
        m = (M-1)//2
        A[M] = ps(pm(h2, pm(B[m+2], cube(B[m]))), pm(A[m-1], cube(A[m+1]))) if m % 2 == 0 \
               else ps(pm(A[m+2], cube(A[m])), pm(h2, pm(B[m-1], cube(B[m+1]))))
    else:
        m = M//2
        B[M] = pm(psc(B[m], INV2), ps(pm(B[m+2], sq(A[m-1])), pm(B[m-2], sq(A[m+1])))) if m % 2 == 0 \
               else pm(psc(A[m], INV2), ps(pm(A[m+2], sq(B[m-1])), pm(A[m-2], sq(B[m+1]))))
for M in range(10, 14):
    f = A[M] if M % 2 else B[M]
    print(f"  m={M:>2}: #F_p roots = {nroots(f)}   (nonzero only for 3|m ⇒ embedded 3-torsion)")
