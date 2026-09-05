#!/usr/bin/env sage
# Independent check of the FORCED e3 sign, from the true power sums V1..V4 (no imposition).
# Expect: e4/p^2 = 1 (both strata); e3/(p*e1) = +1 for p==1 mod4, -1 for p==3 mod4.
B = 7
def true_es(p):
    F = GF(p); E = EllipticCurve(F, [0, B]); n = E.cardinality()
    assert is_prime(n), (p, n)
    G = E.gens()[0]; dl = {}; Q = E(0)
    for d in range(n): dl[Q] = d; Q = Q + G
    def hist(k):
        q = p**k; Fq = GF(q, 'g'); Eq = EllipticCurve(Fq, [0, Fq(B)])
        h = [0]*n; half = (q-1)//2
        for x in Fq:
            r = x**3 + Fq(B)
            if r == 0 or not r.is_square(): continue
            y = r.sqrt()
            for yy in (y, -y):
                c = 1 if yy**half == 1 else -1
                P = Eq(x, yy); T = P; QQ = P
                for _ in range(k-1):
                    QQ = Eq(QQ[0]**p, QQ[1]**p); T = T + QQ
                d = 0 if T == Eq(0) else dl[E(F(T[0]), F(T[1]))]
                h[d] += c
        return h
    zn = [CC(exp(2*CC(pi)*CC(I)*d/n)) for d in range(n)]
    a = 1
    Vs = [sum(hist(k)[d]*zn[(a*d) % n] for d in range(n)) for k in range(1, 5)]
    ps = [-V for V in Vs]                              # power sums p_k = -V_k
    e = [1]
    for kk in range(1, 5):
        s = sum((-1)**(i-1)*e[kk-i]*ps[i-1] for i in range(1, kk+1)); e.append(s/kk)
    e1, e2, e3, e4 = e[1], e[2], e[3], e[4]
    print("p=%2d (p%%4=%d) n=%d :  e4/p^2 = %.6f%+.6fi   e3/(p*e1) = %.6f%+.6fi   [expect e3/(p e1)=%+d]"
          % (p, p % 4, n, e4.real()/p**2, e4.imag()/p**2,
             (e3/(p*e1)).real(), (e3/(p*e1)).imag(), (1 if p % 4 == 1 else -1)))
for p in (13, 43):     # p=13: p==1 mod4 (stratum-C class); p=43: p==3 mod4 (stratum-S class)
    true_es(p)
