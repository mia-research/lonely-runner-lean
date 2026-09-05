# semaev_relation_cost_v2.py  --  run: sage semaev_relation_cost_v2.py [--smoke]
# PREREG_semaev_relation_cost_v2.md. Does the CM quo advantage give more INDEPENDENT factor-base
# relations (lower relation-collection cost), or is it ℤ/n-redundant (automorphism duplicates)?
# Object: within-target-difference matrix M_diff; cost = rank_{ℤ/n}(M_diff) (n=#E, via SNF);
# redundancy detector DIV = rank_ℚ − rank_{ℤ/n}. Exact; no float on the signal path.

from sage.all import *
import random, sys, itertools

SMOKE = ('--smoke' in sys.argv)

# ---- decompositions of a target over a |V|-point factor base (exact enumeration) ----
def decompositions(E, Fpts, m, Tneg):
    """all distinct net-coeff vectors c in Z^|V| with sum_i c_i Fpts[i] = Tneg, via m signed picks."""
    V = len(Fpts); E0 = E(0)
    signed = [(i, 1) for i in range(V)] + [(i, -1) for i in range(V)]
    spt = [(E0 + Fpts[i]) if s == 1 else (E0 - Fpts[i]) for (i, s) in signed]
    out = set()
    for combo in itertools.combinations_with_replacement(range(len(signed)), m):
        S = E0
        for k in combo:
            S = S + spt[k]
        if S == Tneg:
            c = [0]*V
            for k in combo:
                i, s = signed[k]; c[i] += s
            out.add(tuple(c))
    return [list(c) for c in out]

def rankQ_rankZn(rows, n):
    """rank over Q and over Z/n (via Smith normal form invariant factors)."""
    if not rows:
        return 0, 0, 0
    M = matrix(ZZ, rows)
    D = M.smith_form()[0]
    invf = [int(D[i, i]) for i in range(min(D.nrows(), D.ncols()))]
    rQ = sum(1 for d in invf if d != 0)
    rZn = sum(1 for d in invf if d != 0 and gcd(d, n) == 1)
    return rQ, rZn, rQ - rZn

def collect_Mdiff(E, Fpts, m, n, seed, target_cap, thresh):
    """process random targets; accumulate within-target differences; return (T*, rankQ, rankZn, DIV, nq2)."""
    G = E.gens()[0]; N = int(E.order()); random.seed(seed)
    rows = []; Tstar = None; nq2 = 0
    for j in range(target_cap):
        T = int(random.randrange(1, N)) * G
        if T == E(0):
            continue
        decs = decompositions(E, Fpts, m, -T)
        if len(decs) >= 2:
            nq2 += 1
            base = decs[0]
            for c in decs[1:]:
                rows.append([c[i] - base[i] for i in range(len(base))])
        if Tstar is None and rows:
            _, rZn, _ = rankQ_rankZn(rows, n)
            if rZn >= thresh:
                Tstar = j + 1
    rQ, rZn, DIV = rankQ_rankZn(rows, n)
    return dict(Tstar=Tstar, rankQ=rQ, rankZn=rZn, DIV=DIV, nq2=nq2, nrows=len(rows))

def factor_base(E, V, seed):
    G = E.gens()[0]; N = int(E.order()); random.seed(seed)
    F = []
    while len(F) < V:
        P = int(random.randrange(1, N)) * G
        if P != E(0) and all(P[0] != Q[0] for Q in F):
            F.append(P)
    return F

# ---------------- C1 mechanism plants (validate the exact statistic) ----------------
def c1_plants():
    print(">>> C1 mechanism plants:")
    # (a) all-quo=1 -> M_diff empty -> rank 0
    rQ, rZn, DIV = rankQ_rankZn([], 6)
    print("   (a) empty M_diff: rankQ=%d rankZn=%d  [expect 0,0]" % (rQ, rZn))
    # (b) quo=k=3 within one target, differences ℤ/n-independent -> rankZn = k-1 = 2
    rows_b = [[1, 0, 0, 0], [0, 1, 0, 0]]   # two independent differences
    rQ, rZn, DIV = rankQ_rankZn(rows_b, 97)
    print("   (b) 2 indep diffs (n=97 prime): rankQ=%d rankZn=%d  [expect 2,2]" % (rQ, rZn))
    # (c) ℚ-independent but ℤ/n-dependent -> DIV>0 : diag(2,3) over n=6 -> SNF diag(1,6)
    rows_c = [[2, 0], [0, 3]]
    rQ, rZn, DIV = rankQ_rankZn(rows_c, 6)
    print("   (c) [[2,0],[0,3]] over n=6: rankQ=%d rankZn=%d DIV=%d  [expect 2,1,1]" % (rQ, rZn, DIV))
    ok = (rankQ_rankZn([], 6) == (0, 0, 0)
          and rankQ_rankZn(rows_b, 97) == (2, 2, 0)
          and rankQ_rankZn(rows_c, 6) == (2, 1, 1))
    print("   C1 plants %s" % ("PASS" if ok else "FAIL"))
    return ok

def build_curves(p, n_noncm, seed):
    F = GF(p); random.seed(seed); cs = []
    for B in range(1, p):
        cs.append(dict(lab='j0', A=0, B=B, order=int(EllipticCurve(F, [0, B]).order()))); break
    got = tries = 0
    while got < n_noncm and tries < 6000:
        tries += 1
        A = random.randrange(1, p); Bc = random.randrange(1, p)
        if (4*A**3 + 27*Bc**2) % p == 0: continue
        Ec = EllipticCurve(F, [A, Bc]); j = Ec.j_invariant()
        if j == F(0) or j == F(1728): continue
        cs.append(dict(lab='nonCM', A=A, B=Bc, order=int(Ec.order()))); got += 1
    return cs

if __name__ == '__main__':
    sys.stdout.reconfigure(line_buffering=True)
    ok = c1_plants()
    if SMOKE:
        print(">>> smoke: 2 primes, |V|=4, T_cap=120")
        for p in [523, 1033]:
            cs = build_curves(p, 3, seed=1000 + p)
            F = GF(p)
            for c in cs:
                E = EllipticCurve(F, [c['A'], c['B']]); n = c['order']
                Fpts = factor_base(E, 4, seed=7000)
                r = collect_Mdiff(E, Fpts, 3, n, seed=8000, target_cap=120, thresh=3)  # |V|-1=3
                print("   p=%d %-7s #E=%d  T*=%s rankZn=%d DIV=%d nq2=%d"
                      % (p, c['lab'], n, r['Tstar'], r['rankZn'], r['DIV'], r['nq2']))
    print("[gate: PREREG_semaev_relation_cost_v2 — re-gate in flight; run is graded only after clearance]")
