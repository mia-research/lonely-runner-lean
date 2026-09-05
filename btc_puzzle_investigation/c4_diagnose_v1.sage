# Diagnostic for the C4 firing.  Cites: anew_cartier_audit_v1.log "C4" block.
# Question: at which primes does t2+1 fail to break C1, and what is a_p(E) there?
print("prime  arm    p mod 3  a_p(E) mod p   trueTr  pertTr   t2+1 breaks C1")
tested = [(7,"MAIN"),(11,"MAIN"),(19,"MAIN"),(23,"MAIN"),(31,"MAIN"),(43,"MAIN"),
          (5,"CTRL"),(13,"CTRL"),(17,"CTRL"),(29,"CTRL"),(37,"CTRL"),(41,"CTRL")]
co = [2,0,0,1]   # x^3+2, the cubic C4 used for D=3
for p, arm in tested:
    Fp = GF(p); R = PolynomialRing(Fp,'x'); x = R.gen()
    f = R([Fp(c) for c in co])
    if f.discriminant() == 0:
        print("%-6d %-6s  EXCLUDED (disc=0)" % (p, arm)); continue
    E = EllipticCurve(Fp, [0, 2])
    ap = p + 1 - E.cardinality()
    t2 = (2 + p*2)//4
    true_tr = (f**(p - t2))[p-1]
    pert_tr = (f**(p - t2 - 1))[p-1]
    print("%-6d %-6s  %-8d %-14d %-7s %-7s %s"
          % (p, arm, p % 3, ap % p, true_tr, pert_tr, true_tr != pert_tr))
