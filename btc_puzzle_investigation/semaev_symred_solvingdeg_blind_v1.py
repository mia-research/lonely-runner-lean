#!/usr/bin/env sage
# BLIND, exact, non-censoring measurement (PREREG_semaev_symred_solvingdeg_BLIND_v1.md).
# Is the reduced-system Groebner complexity d_gb of the TRUE Semaev coeffs inside the spread over
# random S_3-symmetric coeffs on the same support? Semaev is blinded in a shuffled 17-system pool.
# d_gb = max total degree in the reduced degrevlex Groebner basis (exact GF(p); TERMINATES -> never
# censors, unlike the Macaulay d_solv/d_LF). All integers. No float.
import sys, random as pyr
_ns = dict(globals()); _ns["__name__"] = "h"
exec(open("semaev_elimination_v1.py").read(), _ns)
globals().update({k: v for k, v in _ns.items() if not k.startswith("__")})
exec(open("semaev_symmetric_reduction_lastfall_v1.py").read().split("def main()")[0], globals())

def d_gb_of(gens_list):
    I = gens_list[0].parent().ideal(gens_list)
    return int(max([g.total_degree() for g in I.groebner_basis()]))

def build_pool(p):
    F = GF(p); A=0; B=7; E = EllipticCurve(F,[A,B]); Gp = E.gens()[0]; N = int(E.order())
    rng = pyr.Random(1234+p); Vx=None; tau=None          # SAME frozen construction (two triples)
    for _ in range(3000):
        R = int(rng.randrange(1,N))*Gp
        if R==E(0): continue
        xs=[]; good=True
        for _ in range(2):
            Qa=int(rng.randrange(1,N))*Gp; Qb=int(rng.randrange(1,N))*Gp; Qc=R-Qa-Qb
            if E(0) in (Qa,Qb,Qc): good=False; break
            xs+=[int(Qa[0]),int(Qb[0]),int(Qc[0])]
        if good and len(set(xs))==6 and int(R[0]) not in set(xs): Vx=xs; tau=int(R[0]); break
    planted_e = sym_of([F(v) for v in Vx[:3]])
    P, Rer, ok, S4tau, Rx = build_reduction(F, A, B, tau)
    r_eqs = remainder_eqs(Rer, Vx); support = list(P.monomials())
    pool = [[P] + r_eqs]                                  # index 0 = Semaev
    for j in range(16):                                  # 16 symmetric-random on the same support
        rj = pyr.Random(77000+p+j); Pr = Rer(0)
        for mon in support: Pr += F(rj.randrange(1,p))*mon
        Pr = Pr - Pr(planted_e[0], planted_e[1], planted_e[2])   # re-plant -> consistent
        pool.append([Pr] + r_eqs)
    return F, Rer, pool, ok

def main():
    for p in (307, 2069):
        F, Rer, pool, ok = build_pool(p)
        n = len(pool)                                     # 17
        perm = list(range(n)); pyr.Random(31337+p).shuffle(perm)
        sem_pos = perm.index(0)                           # where Semaev lands (private until reveal)
        shuffled = [pool[perm[i]] for i in range(n)]
        dgbs = [d_gb_of(sys) for sys in shuffled]
        # ---- BLIND VIEW (no labels) ----
        print("p=%d  reduction_correct=%s" % (p, ok))
        print("p=%d  BLIND d_gb multiset (unlabeled, sorted): %s" % (p, sorted(dgbs)))
        sys.stdout.flush()
        # ---- REVEAL ----
        a = dgbs[sem_pos]; rands = [dgbs[i] for i in range(n) if i != sem_pos]
        lo, hi = min(rands), max(rands)
        outcome = "SECP_SPECIFIC_LEVER" if a < lo else ("ANTI" if a > hi else "INVARIANT")
        print("p=%d  REVEAL: Semaev at shuffled pos %d | Semaev d_gb=%d | random d_gb [lo,hi]=[%d,%d] (distinct=%s) | OUTCOME=%s"
              % (p, sem_pos, a, lo, hi, sorted(set(rands)), outcome))
        # ---- secondary d_solv @ Dmax=40 (reported; censored -> 'None', NOT used for the verdict) ----
        dsolv = [last_fall_of(F, sys, list(Rer.gens()), 40)["d_solv"] for sys in shuffled]
        sem_ds = dsolv[sem_pos]; rand_ds = [dsolv[i] for i in range(n) if i != sem_pos]
        print("p=%d  secondary d_solv@Dmax40: Semaev=%s | randoms=%s  (None=censored, ignored for verdict)"
              % (p, sem_ds, rand_ds))
        sys.stdout.flush()
    print("BLIND DONE")

main()
