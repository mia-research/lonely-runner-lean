"""
n=6 BHK (1,-2)S pentagon witness — pin the slant-aware feasible X-window.

Pair (i,j)=(1,-2): rigidity 2r+p=3q (=> r=(3q-p)/2), p,q odd, gcd(p,q)=1, 3p<q, q>=18.
Speeds (reduced): w0=p, w1=q-p, w2=q, w3=r, w4=s ; M=(s-q)/(3 q s).
Cone points: X=frac(r*(2l+1)/(2q)), Y=frac(p*(2l+1)/(2q)).  On X in (1/4,3/4): Y=3/2-2X.

pent_no_good's six conditions (reduced; runner-4 coord X, runner-1 coord Y):
  h39 : X >= 1/6 - r*M
  h40 : Y >= 1/6 - p*M
  h41 : Y <= 1/3 + (q-p)*M
  hxle: X <= 5/6
  h42a: 1/(3s) <= (5/6 - X)/r + (Y - 1/6)/p
  h42b: 1/(3s) <= (5/6 - X)/r + (1/3 - Y)/(q-p)

We (A) check whether some integer l gives a *grid* point (X_l,Y_l) in P (all 6, exact Y_l),
and (B) compute the feasible X-interval ON THE BRANCH Y=3/2-2X and its width vs 1/q,
recording which constraint binds each endpoint.
"""
from math import gcd, floor

def frac(x): return x - floor(x)

def conds(X, Y, p, q, r, s):
    M = (s - q) / (3.0 * q * s)
    return [
        ("h39",  X - (1/6 - r*M)),
        ("h40",  Y - (1/6 - p*M)),
        ("h41",  (1/3 + (q-p)*M) - Y),
        ("hxle", 5/6 - X),
        ("h42a", (5/6 - X)/r + (Y - 1/6)/p - 1/(3*s)),
        ("h42b", (5/6 - X)/r + (1/3 - Y)/(q-p) - 1/(3*s)),
    ]

def feasible_interval_on_branch(p, q, r, s, n=200000):
    """Scan X in (1/4,3/4), Y=3/2-2X; return (lo,hi,binding_lo,binding_hi) of the
    contiguous feasible region (or None)."""
    lo = hi = None
    blo = bhi = None
    xs = [0.25 + (0.5)*(k+0.5)/n for k in range(n)]
    feas = []
    for X in xs:
        Y = 1.5 - 2*X
        cs = conds(X, Y, p, q, r, s)
        ok = all(v >= -1e-12 for _, v in cs)
        feas.append((X, ok, cs))
    # find the widest contiguous feasible run
    best = None
    i = 0
    while i < len(feas):
        if feas[i][1]:
            j = i
            while j < len(feas) and feas[j][1]:
                j += 1
            run = (feas[i][0], feas[j-1][0], i, j-1)
            if best is None or (run[1]-run[0]) > (best[1]-best[0]):
                best = run
            i = j
        else:
            i += 1
    if best is None:
        return None
    Xlo, Xhi, ilo, ihi = best
    # binding constraint at each end = the one closest to 0 just inside
    def binding(idx):
        cs = feas[idx][2]
        return min(cs, key=lambda kv: kv[1])[0]
    return Xlo, Xhi, binding(ilo), binding(ihi)

def grid_witness(p, q, r, s):
    """Does some l give a grid point in P (exact Y_l)?  Return (found, count)."""
    found = 0
    for l in range(-2*q, 2*q):
        X = frac(r*(2*l+1)/(2.0*q))
        Y = frac(p*(2*l+1)/(2.0*q))
        cs = conds(X, Y, p, q, r, s)
        if all(v >= -1e-9 for _, v in cs):
            found += 1
    return found

def main():
    fails_grid = 0
    n_inst = 0
    min_width_ratio = 1e9
    worst = None
    binding_lo = {}
    binding_hi = {}
    for q in range(19, 122, 2):          # q odd
        for p in range(1, q, 2):         # p odd
            if 3*p >= q: continue
            if gcd(p, q) != 1: continue
            if (3*q - p) % 2 != 0: continue
            r = (3*q - p)//2
            if not (q < r): continue
            for s in range(r+1, 3*q+1):
                n_inst += 1
                fw = grid_witness(p, q, r, s)
                if fw == 0:
                    fails_grid += 1
                    if fails_grid <= 8:
                        print(f"  GRID-FAIL q={q} p={p} r={r} s={s}")
                iv = feasible_interval_on_branch(p, q, r, s, n=4000)
                if iv is None:
                    print(f"  NO-INTERVAL q={q} p={p} r={r} s={s}")
                    continue
                Xlo, Xhi, blo, bhi = iv
                w = Xhi - Xlo
                ratio = w * q     # width / (1/q)
                binding_lo[blo] = binding_lo.get(blo, 0) + 1
                binding_hi[bhi] = binding_hi.get(bhi, 0) + 1
                if ratio < min_width_ratio:
                    min_width_ratio = ratio
                    worst = (q, p, r, s, Xlo, Xhi, blo, bhi)
    print(f"\ninstances={n_inst}  grid-witness fails={fails_grid}")
    print(f"min (window width)*q = {min_width_ratio:.4f}   (need >= 1.0 for grid hit)")
    print(f"worst instance (q,p,r,s,Xlo,Xhi,blo,bhi) = {worst}")
    print(f"binding @ lo end: {binding_lo}")
    print(f"binding @ hi end: {binding_hi}")

if __name__ == "__main__":
    main()
