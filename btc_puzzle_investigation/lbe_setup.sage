# Build a small secp-analog GLV curve: y^2 = x^3 + b, p=1 mod 3, prime order n=1 mod3
p = 100003
assert p % 3 == 1 and is_prime(p)
F = GF(p)
found=None
for b in range(1, 200):
    E = EllipticCurve(F, [0, b])
    n = E.order()
    if is_prime(n) and n % 3 == 1:
        found=(b,E,n); break
b,E,n = found
G = E.gens()[0]
# GLV data: beta = cube root of 1 in F_p ; lambda = cube root of 1 mod n with phi(P)=lam*P
beta = [z for z in F if z != 1 and z**3 == 1][0]
# find lambda: phi(x,y)=(beta*x, y). Check which cube root of unity mod n it equals on G
lams = [Integer(z) for z in GF(n) if z != 1 and z**3 == 1]
x,y = G.xy()
phiG = E(beta*x, y)
lam = None
for L in lams:
    if Integer(L)*G == phiG: lam=L; break
print("p=%d b=%d n=%d (n prime, n%%3=%d)"%(p,b,n,n%3))
print("beta=%d (order 3 in F_p), lambda=%d (lam^3=%d mod n), phi(G)=lam*G: %s"%(beta,lam,(lam^3)%n, E(beta*x,y)==lam*G))
save((p,b,n,beta,lam), "/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/a2e97e4b-0256-4ffa-8e2a-5d92f74d8482/scratchpad/curvedata")
