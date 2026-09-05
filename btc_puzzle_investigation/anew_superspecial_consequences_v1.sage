# PHASE 2a -- C = 0 on the new part => Hasse-Witt vanishes there
# => #C(F_p^n) = #E(F_p^n) mod p for ALL n.  Exact, scale-free.
# Pre-committed: "this is a restatement of p-rank 0" is an acceptable answer.
QCAP = 300000
def counts_Fq_curve(F, fco):
    q = F.cardinality(); g4 = gcd(4, q - 1); e4 = (q-1)//g4; e2 = (q-1)//2
    nC = 1; nE = 1
    for x in F:
        v = F(0)
        for c in reversed(fco): v = v * x + F(c)
        if v == 0: nC += 1; nE += 1
        else:
            if v**e4 == 1: nC += g4
            if v**e2 == 1: nE += 2
    return nC, nE

print("="*96); print("PHASE 2a : #C(F_p^n) = #E(F_p^n) mod p ?   (q capped at %d)" % QCAP); print("="*96)
CUB = [("x^3+7",[7,0,0,1]), ("x^3+2x+5",[5,2,0,1]), ("x^3+x+1",[1,1,0,1]), ("x^3-x+3",[3,-1,0,1])]
def arm(tag, primes, nmax):
    bad = tot = 0
    for p in primes:
        for nm, co in CUB:
            R = PolynomialRing(GF(p),'x')
            if R([GF(p)(c) for c in co]).discriminant() == 0: continue
            row = []
            for n in range(1, nmax+1):
                if p**n > QCAP: break
                nC, nE = counts_Fq_curve(GF(p**n,'g'), co)
                ok = bool((nC - nE) % p == 0); row.append(ok); tot += 1
                if not ok: bad += 1
            print("  %s p=%-3d %-10s  n=1..%d : %s" % (tag, p, nm, len(row), row))
    return bad, tot
bm, tm = arm("MAIN", (7, 11, 19, 23, 31, 43), 5)
print()
bc, tc = arm("CTRL", (5, 13, 17, 29), 4)
print("\n  MAIN : %d/%d congruences HOLD" % (tm-bm, tm))
print("  CTRL : %d/%d hold -> %d FAIL   [control MUST fail, else the congruence is vacuous]" % (tc-bc, tc, bc))
