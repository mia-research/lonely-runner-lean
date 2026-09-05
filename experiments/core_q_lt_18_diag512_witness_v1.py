"""De-risk BHK Case 5.2.12.x diagonal sorries in core_q_lt_18 (n=6).

Reduced coords (g=1; g only scales time, fractional positions unchanged):
  runner 0: n0 = p          (BHK v1 = p/q)
  runner 1: n1 = q - p      (BHK v2)
  runner 2: n2 = q          (BHK v3 = 1)
  runner 3: n3 = q + p = r  (BHK v4, diagonal)
  runner 4: n4 = s          (BHK v5)
A time theta is "covered by runner i" iff circDist(n_i*theta) < 1/6, i.e.
frac(n_i*theta) in (1/6,5/6)^c.  hcover: every theta covered by some runner.
A LONELY witness theta: frac(n_i*theta) in [1/6,5/6] for ALL i  -> contradiction.

For each case we (A) find the upper bound on s from a 01234-gap interval, then
(B) for each surviving s, find an explicit rational lonely witness theta.
"""
from fractions import Fraction as F

def frac(x):
    return x - (x.numerator // x.denominator)

def cdist(x):
    f = frac(x)
    return min(f, 1 - f)

def lonely(ns, theta):
    return all(cdist(n*theta) >= F(1,6) for n in ns)

def covered_only_by(ns, theta, idx):
    """True if runner idx covers theta and no other runner does."""
    cov = [i for i,n in enumerate(ns) if cdist(n*theta) < F(1,6)]
    return cov == [idx]

# (p, q, r=p+q, label, list of s values BHK pins to)
cases = [
    (1,5,6, "5.2.12.1", [13]),
    (1,6,7, "5.2.12.2", [13]),
    (1,7,8, "5.2.12.3", [9]),
    (1,12,13,"5.2.12.5", [14,15]),
    (1,10,11,"Claim21 q=10", None),   # determine surviving s
    (2,7,9, "p=2 q=7", None),
    (2,9,11,"p=2 q=9", None),
]

def find_lonely_witness(ns, max_den=400):
    """Search rational theta = a/d with small denominator for a lonely time."""
    best = []
    for d in range(2, max_den+1):
        for a in range(1, d):
            th = F(a, d)
            if lonely(ns, th):
                best.append(th)
        if best:
            return best[:8], d
    return None, None

def upper_bound_s_from_gap(p,q,r):
    """Find a 01234-gap [a,b] (runners 0..3 away on whole interval) of max length;
    s <= q/(3L) where L = b-a. Brute force over rational endpoints near BHK's."""
    ns0123 = [p, q-p, q, r]
    # scan candidate intervals: pick fine grid, find maximal run where all 4 away
    N = 720
    away = []
    for k in range(N):
        th = F(k, N)
        ok = all(cdist(n*th) >= F(1,6) for n in ns0123)
        away.append(ok)
    # longest run (cyclic)
    best_len = 0; best_run=None
    ext = away + away
    i=0
    while i < N:
        if ext[i]:
            j=i
            while j < i+N and ext[j]:
                j+=1
            runlen = j - i
            if runlen > best_len:
                best_len = runlen; best_run=(i % N, (j-1)%N, runlen)
            i = j
        else:
            i+=1
    L = F(best_len, N)  # approx length (grid units); true length >= this
    return best_run, L

for p,q,r,label,svals in cases:
    print(f"\n=== ({p},{q},{r})  {label} ===")
    run, L = upper_bound_s_from_gap(p,q,r)
    if run:
        a,b,rl = run
        sbound = F(q,1)/(3*L) if L>0 else None
        print(f"  longest 0123-away run (grid/720): [{a}/720,{b}/720] len~{float(L):.4f}"
              f" -> s <~ q/(3L) ~ {float(sbound):.3f}" if sbound else "  no gap")
    # determine surviving s
    if svals is None:
        cand = []
        for s in range(r+1, 4*q+2):
            run2,L2 = upper_bound_s_from_gap(p,q,r)  # same gap; check coverability
            cand.append(s)
        # better: list s in (r, sbound] and whether a lonely witness exists
        smax = int(float(F(q,1)/(3*L))) if L>0 else 4*q
        svals = list(range(r+1, smax+1))
        print(f"  surviving s in ({r},{smax}]: {svals}")
    for s in svals:
        ns = [p, q-p, q, r, s]
        wit, d = find_lonely_witness(ns)
        if wit:
            w = wit[0]
            poss = [frac(n*w) for n in ns]
            print(f"  s={s}: LONELY theta={w} (den {d}); fracs="
                  f"{[f'{float(x):.3f}' for x in poss]}")
        else:
            print(f"  s={s}: NO lonely witness found (<=den400)  !!")
