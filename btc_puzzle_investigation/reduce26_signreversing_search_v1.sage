#!/usr/bin/env sage
"""reduce26_signreversing_search_v1.sage -- after the E[2] parity obstruction, search for the REAL
mechanism of Sum_t chi_2(g(t)F(t)) = 0.

Rigorous result (reduce26 reasoning): E[2]-translations do NOT descend to F_p-rational involutions of
P^1 when n is odd (sigma_T F_p-rational on E/iota <=> T in E[2](F_p) = {O}). So the doc's §5 lead is
killed. But the sum vanishes empirically -- SOMETHING makes it 0. Find what.

Approach: enumerate the quotient P^1(F_p) via the iota-invariant coordinate t = x(P) + x(R-P),
recording chi_2(g(t) F(t)) = chi_2(split/inert) * chi_2(y1 y2) at each t. Then:
  (a) confirm Sum = 0;
  (b) search ALL F_p-rational involutions of P^1 (Mobius t -> (at+b)/(ct-a), a^2+bc != 0) for one that
      sign-reverses chi_2(gF) -- if none exists, the vanishing is NOT pointwise-antisymmetric, and we
      look for (c) a factorization of gF giving a classical exact-zero character sum.
"""
from sage.all import GF, EllipticCurve, ZZ
from collections import defaultdict
import itertools


def chi2(a, p):
    a = int(a) % p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


def quotient_sign_table(p, A, B, e=3):
    """For E:y^2=x^3+Ax+B, R=[e]G, build the table over the iota-invariant coord t=x(P)+x(R-P) of
    (chi_2(g) = split/inert sign, chi_2(F)=chi_2(y1 y2)). Returns dict t -> (cg, cF, cgF) and the sum."""
    Fp = GF(p); Fp2 = GF(p**2, 'a')
    E = EllipticCurve(Fp, [A, B])
    n = E.order()
    G = next(P for P in E if P.order() == n)
    R = e*G
    if R.is_zero(): return None
    E2 = E.change_ring(Fp2); R2 = E2(R[0], R[1])
    # enumerate fibres via P1 in E2 with the trace condition; record t = x1 + x(R-P1), cg, cF
    # iota_x as a function: given P1=(x1,y1), x(R-P1) computed by group law over Fp2.
    A4 = ZZ(E.a4()); xR = ZZ(R[0]); yR = ZZ(R[1])
    def x_of_RminusP(P1):
        x1, y1 = P1[0], P1[1]
        # -P1 = (x1,-y1); R + (-P1): lam = (yR - (-y1))/(xR - x1); x3 = lam^2 - x1 - xR
        if x1 == xR: return None
        lam = (yR + y1) / (xR - x1)
        return lam**2 - x1 - xR
    seen = set(); table = {}
    for x1 in Fp2:
        rhs = x1**3 + A4*x1 + B
        if not rhs.is_square(): continue
        y1 = rhs.sqrt()
        for sgn in (1,-1):
            P1 = E2(x1, sgn*y1)
            P2 = R2 - P1
            if P1.is_zero() or P2.is_zero(): continue
            inFp1 = (P1[0] in Fp) and (P1[1] in Fp)
            Pf = E2(P1[0]**p, P1[1]**p)
            is_conj = (Pf == P2) and not inFp1
            is_rat = inFp1 and (E2(R2[0],R2[1]) - P1)[0] in Fp and (not (E2(R2[0],R2[1]) - P1).is_zero())
            if not (is_conj or is_rat): continue
            key = frozenset((tuple(P1), tuple(P2)))
            if key in seen: continue
            seen.add(key)
            xRmP = x_of_RminusP(P1)
            if xRmP is None: continue
            t = P1[0] + xRmP          # iota-invariant coord (in Fp2 but should be F_p)
            if t not in Fp: continue   # only F_p fibres matter
            t = Fp(t)
            prod_y = P1[1]*P2[1]
            if prod_y != prod_y**p: continue
            cF = chi2(prod_y, p)
            cg = 1 if is_rat else -1
            table[tuple(map(int,(t,)))] = (cg, cF, cg*cF)
    return table, R


if __name__ == "__main__":
    for (p,A,B,lab) in [(43,0,7,"j=0"),(79,1,4,"generic"),(73,1,3,"eps+1")]:
        print("\n"+"="*60); print("p=%d E:y^2=x^3+%dx+%d (%s)"%(p,A,B,lab))
        for e in (1,2,3,5):
            res = quotient_sign_table(p,A,B,e=e)
            if res is None: continue
            table, R = res
            if not table: print("  e=%d: empty table"%e); continue
            S = sum(v[2] for v in table.values())
            print("  R=[%d]G: %d quotient pts, Sum chi_2(gF) = %d"%(e,len(table),S))
            if p > 50: continue   # involution search only for small p
            # build sign array over P^1(F_p): index by t in F_p (plus infinity)
            # represent t as integer 0..p-1, and infinity as p.
            def idx(t):
                return p if t is None else (int(t) if t != 'inf' else p)
            # the table keys are F_p elements; collect signs
            signs = {}
            for (t,), (cg,cF,cgF) in table.items():
                signs[t] = cgF
            ts = sorted(signs.keys())
            # search Mobius involutions t -> (a t + b)/(c t + d) with matrix [[a,b],[c,d]] of order 2,
            #   i.e. trace 0: a + d = 0 mod p. So d = -a. t -> (a t + b)/(c t - a), a^2 + bc != 0.
            #   test if chi_2(gF(sigma t)) = -chi_2(gF(t)) for all t in our table.
            found = []
            for a in range(p):
                for b in range(p):
                    for c in range(p):
                        if (a*a + b*c) % p == 0: continue   # degenerate
                        ok = True; has_fixed = False
                        for t in ts:
                            denom = (c*int(t) - a) % p
                            if denom == 0:
                                st = None  # infinity
                            else:
                                st = (a*int(t) + b) * pow(denom,-1,p) % p
                            if st not in signs: ok = False; break
                            if st == t: has_fixed = True
                            if signs[st] != -signs[t]: ok = False; break
                        # also check the infinity <-> -a/c mapping if relevant (skip for simplicity)
                        if ok and not has_fixed:
                            found.append((a,b,c))
                        if len(found) > 5: break
                    if len(found) > 5: break
                if len(found) > 5: break
            print("    F_p-rational sign-reversing Mobius involutions (no fixed pt): %s" %
                  (found if found else "NONE"))
