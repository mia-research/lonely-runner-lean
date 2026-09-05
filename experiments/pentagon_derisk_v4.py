"""
v4 (analytic, exact): test the antidiag-STYLE construction for (1,±2).
Grid spacing 1/e, e = gcd(2r∓p, q). Points lie on Y = frac(slope*X - c), slope=±2.
Both X,Y move on a 1/e grid (gcd(r,e)=gcd(p,e)=1). A length-1/e X-window over
which the line stays in P gives a guaranteed grid point in P (grid_hit).
Decisive: is max contiguous X-run of (line ∩ P) ALWAYS >= 1/e (e>=6)?
Compute the run analytically: for each wrap-branch n, Y=slope*X-c-n is affine,
P's 6 linear constraints -> an X-interval. Max length over n.
"""
from math import gcd
from fractions import Fraction as F

def frac(x):
    return x - (x.numerator // x.denominator)

def S(l, p, q, r):
    u = 2 * l + 1
    return frac(F(r * u, 2 * q)), frac(F(p * u, 2 * q))

XLO, XHI, YLO, YHI = F(1, 6), F(1, 2), F(1, 6), F(1, 3)
def inR(X, Y): return XLO <= X <= XHI and YLO <= Y <= YHI
def cap_R_empty(p, q, r): return all(not inR(*S(l, p, q, r)) for l in range(q))
def in_G(i, j, p, q, r):
    return any((m*r) % q == i % q and (m*p) % q == j % q for m in range(q))
def is_pair(ii, jj, p, q, r):
    if not in_G(ii, jj, p, q, r): return False
    for k in range(-abs(ii), abs(ii)+1):
        for l in range(-abs(jj), abs(jj)+1):
            if (k, l) == (0, 0) or (abs(k) == abs(ii) and abs(l) == abs(jj)): continue
            if in_G(k, l, p, q, r): return False
    return True
def survivors(ii, jj, qmax):
    out = []
    for q in range(18, qmax+1):
        for p in range(1, q):
            if 3*p >= q or gcd(p, q) != 1: continue
            for r in range(q+1, (3*q)//2+1):
                if 2*r >= 3*q: continue
                if is_pair(ii, jj, p, q, r) and cap_R_empty(p, q, r): out.append((p, q, r))
    return out

def line_run(p, p2, q, r, s, c, slope):
    """max contiguous X-length of {X in [1/6,5/6] : (X, frac(slope*X-c)) in P}."""
    e1 = F(r*(s-q), 3*q*s); e0 = F(p*(s-q), 3*q*s); e2 = F(p2*(s-q), 3*q*s)
    inv3s = F(1, 3*s)
    best = F(0)
    for n in range(-4, 5):
        # Y = slope*X - c - n ; collect X lower/upper bounds from the 6 P-constraints
        Lo = [F(1, 6) - e1, F(1, 6)]          # c1: X>=1/6-e1 ; branch: X>=1/6
        Hi = [F(5, 6), F(5, 6)]               # c4: X<=5/6 ; branch: X<=5/6
        # c2: Y >= 1/6 - e0  -> slope*X >= 1/6 - e0 + c + n
        rhs = F(1, 6) - e0 + c + n
        (Lo if slope > 0 else Hi).append(F(rhs, slope))
        # c3: Y <= 1/3 + e2  -> slope*X <= 1/3 + e2 + c + n
        rhs = F(1, 3) + e2 + c + n
        (Hi if slope > 0 else Lo).append(F(rhs, slope))
        # c5: (5/6-X)/r + (Y-1/6)/p >= 1/(3s); A5*X + B5 >= 0
        A5 = -F(1, r) + F(slope, p)
        B5 = F(5, 6*r) + (-c - n - F(1, 6)) / p - inv3s
        if A5 > 0: Lo.append(-B5 / A5)
        elif A5 < 0: Hi.append(-B5 / A5)
        elif B5 < 0: continue
        # c6: (5/6-X)/r + (1/3-Y)/p2 >= 1/(3s); A6*X + B6 >= 0
        A6 = -F(1, r) - F(slope, p2)
        B6 = F(5, 6*r) + (F(1, 3) + c + n) / p2 - inv3s
        if A6 > 0: Lo.append(-B6 / A6)
        elif A6 < 0: Hi.append(-B6 / A6)
        elif B6 < 0: continue
        lo = max(Lo); hi = min(Hi)
        if hi > lo: best = max(best, hi - lo)
    return best

for (ii, jj) in [(1, 2), (1, -2)]:
    survs = survivors(ii, jj, 60)
    slope = jj
    print(f"\n=== pair ({ii},{jj}): {len(survs)} survivors (q<61) ===")
    e_lt6 = 0; e_dist = {}
    worst_margin = None; worst_case = None; n_fail = 0; cmp_tot = 0
    for (p, q, r) in survs:
        D = 2*r - p if jj == 2 else 2*r + p
        e = gcd(abs(D), q)
        e_dist[e] = e_dist.get(e, 0) + 1
        if e < 6: e_lt6 += 1
        X0, Y0 = S(0, p, q, r); c = frac(slope*X0 - Y0)
        inv = F(1, e)
        for p2 in range(p+1, q):
            for s in range(r+1, 3*q+1):
                cmp_tot += 1
                run = line_run(p, p2, q, r, s, c, slope)
                margin = run - inv
                if run < inv: n_fail += 1
                if worst_margin is None or margin < worst_margin:
                    worst_margin = margin
                    worst_case = (p, q, r, p2, s, e, float(run), float(inv))
    print(f"  e=gcd(2r∓p,q): <6 = {e_lt6}/{len(survs)}; e-dist={dict(sorted(e_dist.items()))}")
    print(f"  completions={cmp_tot}; runs(line∩P) < 1/e : {n_fail}")
    print(f"  worst margin (maxrun - 1/e) = {float(worst_margin):.6f}")
    print(f"  worst case (p,q,r,p2,s,e,maxrun,1/e) = {worst_case}")
