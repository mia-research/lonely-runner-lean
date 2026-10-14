r"""
du2_nonrep_endtoend_v1 -- witness construction for the n=8 DROPPED-UNIT leaf with
NON-representative speeds.

E = { e_rho = 8 q_rho + rho : rho in R_non } u {8 m1, 8 m2}.
The witness b is LOCATED by exact interval algebra (S minus B_m1 minus B_m2), never
by a search over b; the search is used only as a control on a subsample.
It is then CHECKED in pure integer arithmetic: e*k mod 8L in [L, 7L] for every e in E.

Also reports  |S| - |B_m1 u B_m2|  exactly, and the sharpened B-lemma bound
   |B_m1 u B_m2| <= 1/2 - gcd(m1,m2)/(4 max(m1,m2)).
"""
import sys, random
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd

Z8 = frozenset(range(8))
UNITS = frozenset({1, 3, 5, 7})
BAD = {(e, t): frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))
       for e in range(8) for t in range(8)}


def merge(iv):
    iv = sorted(iv); out = []
    for a, b in iv:
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def meas(iv):
    return sum((b - a for a, b in iv), F(0))


def Bm(m):
    return merge([(F(8*j-1, 8*m), F(8*j+1, 8*m)) for j in range(m+1)
                  if F(8*j+1, 8*m) > 0 and F(8*j-1, 8*m) < 1]
                 + [(F(0), F(1, 8*m)), (F(8*m-1, 8*m), F(1))])


def Bm_clip(m):
    out = []
    for a, b in Bm(m):
        x, y = max(a, F(0)), min(b, F(1))
        if x < y:
            out.append((x, y))
    return merge(out)


def complement(iv):
    out, cur = [], F(0)
    for a, b in iv:
        if cur < a:
            out.append((cur, a))
        cur = max(cur, b)
    if cur < 1:
        out.append((cur, F(1)))
    return out


def inter(A, B):
    out, i, j = [], 0, 0
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if lo < hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out


def safe_cells(Enon):
    pts = {F(0), F(1)}
    for e in Enon:
        for j in range(1, e):
            pts.add(F(j, e))
    p = sorted(pts); out = []
    for a, b in zip(p, p[1:]):
        cov = set()
        for e in Enon:
            v = e * a
            cov |= BAD[(e % 8, (v.numerator // v.denominator) % 8)]
        U = Z8 - cov
        if U:
            out.append((a, b, frozenset(U)))
    return out


def lcm_all(v):
    L = 1
    for x in v:
        L = L * x // gcd(L, x)
    return L


def run(Enon, m1, m2, control=False):
    E = sorted(Enon) + [8*m1, 8*m2]
    assert len(set(E)) == 7
    L = lcm_all(E)
    B = merge(Bm_clip(m1) + Bm_clip(m2))
    good = complement(B)
    cells = safe_cells(Enon)
    Sint = merge([(a, b) for a, b, _ in cells])
    surplus = meas(Sint) - meas(B)
    picked = None
    for a, b, U in cells:
        for lo, hi in inter([(a, b)], good):
            v = lo * L
            assert v.denominator == 1, ("integrality", E, lo, L)
            bb = v.numerator
            if F(bb, L) < hi:
                picked = (bb, U); break
        if picked: break
    if picked is None:
        return dict(ok=False, why="empty S\\B", E=E, L=L, surplus=surplus)
    b0, U = picked
    N = 8*L
    for r in sorted(U):
        k = b0 + r*L
        vals = [(e*k) % N for e in E]
        if all(L <= v <= 7*L for v in vals):
            slack = min(min(v, N-v) for v in vals)
            res = dict(ok=True, E=E, L=L, b=b0, r=r, k=k,
                       slack=F(slack, N), surplus=surplus,
                       gcdbound=F(1,2) - F(gcd(m1,m2), 4*max(m1,m2)),
                       measB=meas(B), measS=meas(Sint))
            if control and L <= 200000:
                brute = None
                for bb in range(L):
                    cov = 0
                    for e in E:
                        t = (e*bb)//L
                        for rr in range(8):
                            if (e*rr+t) % 8 in (0, 7):
                                cov |= 1 << rr
                    if cov != 255:
                        brute = bb; break
                res['control_first_safe_b'] = brute
            return res
    return dict(ok=False, why="uncovered r not a witness", E=E, L=L, b=b0, U=sorted(U))


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "exh":
        Q, M = int(sys.argv[2]), int(sys.argv[3])
        pairs = [X for X in combinations(range(1, 8), 2) if set(X) & UNITS]
        n = 0; fails = []; worst_s = None; worst_slack = None
        for A in pairs:
            R = sorted(set(range(1, 8)) - set(A))
            for qv in product(range(Q+1), repeat=5):
                Enon = [8*q + r for q, r in zip(qv, R)]
                if len(set(Enon)) < 5:
                    continue
                for m1 in range(1, M+1):
                    for m2 in range(m1+1, M+1):
                        d = run(Enon, m1, m2)
                        n += 1
                        if not d['ok']:
                            fails.append(d); continue
                        if worst_s is None or d['surplus'] < worst_s[0]:
                            worst_s = (d['surplus'], d['E'])
                        if worst_slack is None or d['slack'] < worst_slack[0]:
                            worst_slack = (d['slack'], d['E'])
        print(f"EXHAUSTIVE q<= {Q}, 1<=m1<m2<= {M}: {n} tuples, {len(fails)} failures")
        for f in fails[:10]:
            print("   FAIL", f)
        print(f"  minimum |S| - |B_m1 u B_m2| = {worst_s[0]} = {float(worst_s[0]):.6f}"
              f"  at E = {worst_s[1]}")
        print(f"  minimum witness slack min_e ||e k / 8L|| = {worst_slack[0]}"
              f" = {float(worst_slack[0]):.6f}  at E = {worst_slack[1]}   (need >= 1/8)")
    elif mode == "rnd":
        NS, Q, M, = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        rnd = random.Random(9182736)
        pairs = [X for X in combinations(range(1, 8), 2) if set(X) & UNITS]
        n = 0; fails = []; worst_s = None; ctrl_ok = 0; ctrl_n = 0
        for i in range(NS):
            A = rnd.choice(pairs)
            R = sorted(set(range(1, 8)) - set(A))
            Enon = [8*rnd.randint(0, Q) + r for r in R]
            if len(set(Enon)) < 5:
                continue
            m1, m2 = sorted(rnd.sample(range(1, M+1), 2))
            ctl = (i % 5 == 0)
            d = run(Enon, m1, m2, control=ctl)
            n += 1
            if not d['ok']:
                fails.append(d); continue
            if ctl and 'control_first_safe_b' in d:
                ctrl_n += 1
                ctrl_ok += (d['control_first_safe_b'] is not None)
            if worst_s is None or d['surplus'] < worst_s[0]:
                worst_s = (d['surplus'], d['E'])
        print(f"RANDOM {n} tuples, q<= {Q}, m<= {M}: {len(fails)} failures")
        for f in fails[:10]:
            print("   FAIL", f)
        print(f"  minimum |S| - |B_m1 u B_m2| = {worst_s[0]} = {float(worst_s[0]):.6f}"
              f"  at E = {worst_s[1]}")
        print(f"  brute-force control (independent integer scan for a safe b): "
              f"{ctrl_ok}/{ctrl_n} found one")
    elif mode == "one":
        Enon = [int(v) for v in sys.argv[2].split(",")]
        m1, m2 = int(sys.argv[3]), int(sys.argv[4])
        d = run(Enon, m1, m2, control=True)
        for k, v in d.items():
            print(f"  {k} = {v}")
