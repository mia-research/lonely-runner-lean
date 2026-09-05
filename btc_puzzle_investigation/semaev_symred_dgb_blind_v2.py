#!/usr/bin/env sage
# BLIND, exact, non-censoring (v2). Fixes v1: (a) d_gb (Groebner max degree) ONLY -- the Macaulay
# d_solv was unreliable (censored >34 while the true d_gb=2); (b) random systems VARIETY-MATCHED to
# Semaev (forced to vanish at BOTH planted decomposition points, so quo matches -- removes the v1
# confound where randoms hit only 1 forced point); (c) recompute unreduced-vs-reduced with d_gb to
# recheck the earlier "reduction raises the degree" claim. Exact GF(p); no float.
import sys, random as pyr
_ns = dict(globals()); _ns["__name__"] = "h"
exec(open("semaev_elimination_v1.py").read(), _ns)
globals().update({k: v for k, v in _ns.items() if not k.startswith("__")})
exec(open("semaev_symmetric_reduction_lastfall_v1.py").read().split("def main()")[0], globals())

def d_gb_and_quo(gens_list):
    I = gens_list[0].parent().ideal(gens_list)
    dg = int(max([g.total_degree() for g in I.groebner_basis()]))
    dim = int(I.dimension()); q = int(I.vector_space_dimension()) if dim == 0 else None
    return dg, q

def match_two(Pr, mons, pt1, pt2, F):
    """subtract a 2-term correction so Pr vanishes at pt1 AND pt2 (exact GF(p) 2x2 solve)."""
    for i in range(len(mons)):
        for j in range(i+1, len(mons)):
            M = matrix(F, [[mons[i](*pt1), mons[j](*pt1)], [mons[i](*pt2), mons[j](*pt2)]])
            if M.determinant() != 0:
                c = M.solve_right(vector(F, [Pr(*pt1), Pr(*pt2)]))
                return Pr - c[0]*mons[i] - c[1]*mons[j]
    return None

def main():
    for p in (307, 2069):
        F = GF(p); A=0; B=7; E = EllipticCurve(F,[A,B]); Gp = E.gens()[0]; N = int(E.order())
        rng = pyr.Random(1234+p); Vx=None; tau=None
        for _ in range(3000):
            R = int(rng.randrange(1,N))*Gp
            if R==E(0): continue
            xs=[]; good=True
            for _ in range(2):
                Qa=int(rng.randrange(1,N))*Gp; Qb=int(rng.randrange(1,N))*Gp; Qc=R-Qa-Qb
                if E(0) in (Qa,Qb,Qc): good=False; break
                xs+=[int(Qa[0]),int(Qb[0]),int(Qc[0])]
            if good and len(set(xs))==6 and int(R[0]) not in set(xs): Vx=xs; tau=int(R[0]); break
        pt1 = tuple(sym_of([F(v) for v in Vx[0:3]])); pt2 = tuple(sym_of([F(v) for v in Vx[3:6]]))
        P, Rer, ok, S4tau, Rx = build_reduction(F, A, B, tau)
        r_eqs = remainder_eqs(Rer, Vx); support = list(P.monomials())
        # ---- (A) does symmetrization help? unreduced-x vs reduced-e, d_gb (reliable) ----
        X1,X2,X3 = Rx.gens(); gX = lambda xi: prod([xi - F(v) for v in Vx])
        un_dg, un_q = d_gb_and_quo([S4tau, gX(X1), gX(X2), gX(X3)])
        rd_dg, rd_q = d_gb_and_quo([P] + r_eqs)
        print("p=%d  reduction_correct=%s" % (p, ok))
        print("p=%d  (A) UNREDUCED-x Semaev: d_gb=%d quo=%s  |  REDUCED-e Semaev: d_gb=%d quo=%s  ->  reduction %s the Groebner degree"
              % (p, un_dg, un_q, rd_dg, rd_q, ("LOWERS" if rd_dg < un_dg else ("RAISES" if rd_dg > un_dg else "leaves")))); sys.stdout.flush()
        # ---- (B) BLIND coefficient test, VARIETY-MATCHED (all forced to vanish at pt1 AND pt2) ----
        pool = [[P] + r_eqs]; quos = [rd_q]                # index 0 = Semaev (already quo=2)
        for j in range(16):
            rj = pyr.Random(77000+p+j); Pr = Rer(0)
            for mon in support: Pr += F(rj.randrange(1,p))*mon
            Pm = match_two(Pr, support, pt1, pt2, F)        # force vanish at both planted points
            pool.append([Pm] + r_eqs)
        perm = list(range(len(pool))); pyr.Random(31337+p).shuffle(perm)
        sem_pos = perm.index(0); shuffled = [pool[perm[i]] for i in range(len(pool))]
        res = [d_gb_and_quo(sysk) for sysk in shuffled]
        dgbs = [r[0] for r in res]; qs = [r[1] for r in res]
        print("p=%d  (B) BLIND d_gb multiset (unlabeled, sorted): %s" % (p, sorted(dgbs)))
        print("p=%d  (B) BLIND quo multiset (should be matched): %s" % (p, sorted([q for q in qs if q is not None]))); sys.stdout.flush()
        a = dgbs[sem_pos]; rands = [dgbs[i] for i in range(len(pool)) if i != sem_pos]
        lo, hi = min(rands), max(rands)
        outcome = "SECP_SPECIFIC_LEVER (a<lo)" if a < lo else ("ANTI (a>hi)" if a > hi else "INVARIANT (lo<=a<=hi)")
        print("p=%d  (B) REVEAL: Semaev pos=%d d_gb=%d quo=%s | random d_gb distinct=%s [lo,hi]=[%d,%d] | quo(Semaev)=%s randquo_distinct=%s | OUTCOME=%s"
              % (p, sem_pos, a, qs[sem_pos], sorted(set(rands)), lo, hi, qs[sem_pos],
                 sorted(set([qs[i] for i in range(len(pool)) if i != sem_pos and qs[i] is not None])), outcome)); sys.stdout.flush()
    print("BLIND v2 DONE")

main()
