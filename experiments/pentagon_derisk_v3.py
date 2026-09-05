"""
v3: pin the CONSTRUCTIVE grid recipe for the (1,±2) pentagon witness, so Brick 2
can be formalized as a slope-±2 analog of `bhk_prop11_antidiag_circle_witness`
(R -> P-subrectangle) rather than an invented argument.

Questions:
  Q1. Invariant line. For (1,2): is  2X - Y  ≡ const (mod 1) over all l? slope 2.
      For (1,-2): is 2X + Y ≡ const (mod 1)? slope -2.  (X=fract(r u/2q),Y=fract(p u/2q),u=2l+1)
  Q2. Clean P-subrectangle.  Rp := [1/2, 5/6 - r/(3s)] x [1/6, 1/3].
      (a) Is Rp ⊆ P for every survivor+completion?   (b) Does Rp contain >=1 witness S(l)?
  Q3. Grid spacing.  Mirror antidiag: invariant combo coeff D=|2r∓p|, e=gcd(D,2q)
      style.  What is the actual spacing of the witness coordinate, and is the
      Rp-segment length >= that spacing (so a grid-hit pigeonhole lands a point)?
"""
from math import gcd
from fractions import Fraction as F

def frac(x):
    return x - (x.numerator // x.denominator)

def S(l, p, q, r):
    u = 2 * l + 1
    return frac(F(r * u, 2 * q)), frac(F(p * u, 2 * q))

XLO, XHI, YLO, YHI = F(1, 6), F(1, 2), F(1, 6), F(1, 3)

def inR(X, Y):
    return XLO <= X <= XHI and YLO <= Y <= YHI

def cap_R_empty(p, q, r):
    return all(not inR(*S(l, p, q, r)) for l in range(q))

def in_G(i, j, p, q, r):
    return any((m * r) % q == i % q and (m * p) % q == j % q for m in range(q))

def is_pair(ii, jj, p, q, r):
    if not in_G(ii, jj, p, q, r):
        return False
    for k in range(-abs(ii), abs(ii) + 1):
        for l in range(-abs(jj), abs(jj) + 1):
            if (k, l) == (0, 0) or (abs(k) == abs(ii) and abs(l) == abs(jj)):
                continue
            if in_G(k, l, p, q, r):
                return False
    return True

def in_P(X, Y, p, p2, q, r, s):
    e1 = F(r * (s - q), 3 * q * s)
    e0 = F(p * (s - q), 3 * q * s)
    e2 = F(p2 * (s - q), 3 * q * s)
    return (X >= F(1, 6) - e1 and Y >= F(1, 6) - e0 and Y <= F(1, 3) + e2
            and X <= F(5, 6)
            and F(1, 3 * s) <= (F(5, 6) - X) / r + (Y - F(1, 6)) / p
            and F(1, 3 * s) <= (F(5, 6) - X) / r + (F(1, 3) - Y) / p2)

def survivors(ii, jj, qmax):
    out = []
    for q in range(18, qmax + 1):
        for p in range(1, q):
            if 3 * p >= q or gcd(p, q) != 1:
                continue
            for r in range(q + 1, (3 * q) // 2 + 1):
                if 2 * r >= 3 * q:
                    continue
                if is_pair(ii, jj, p, q, r) and cap_R_empty(p, q, r):
                    out.append((p, q, r))
    return out

# ---- Q1: invariant line --------------------------------------------------
def check_invariant(ii, jj, survs):
    bad = 0
    for (p, q, r) in survs:
        vals = set()
        for l in range(q):
            X, Y = S(l, p, q, r)
            # slope j/i = jj for i=1: combination jj*X - Y  (1,2)->2X-Y ; (1,-2)-> -2X - Y
            w = frac(jj * X - Y) if (jj * X - Y) >= 0 else frac(jj * X - Y)
            vals.add(frac((jj * X - Y) % 1))
        if len(vals) > 1:
            bad += 1
    return bad

# ---- Q2/Q3: subrectangle Rp = [1/2, 5/6 - r/(3s)] x [1/6,1/3] -------------
def Rp_bounds(q, r, s):
    return F(1, 2), F(5, 6) - F(r, 3 * s), F(1, 6), F(1, 3)

def Rp_subset_P(p, p2, q, r, s):
    xlo, xhi, ylo, yhi = Rp_bounds(q, r, s)
    if xhi < xlo:
        return None  # degenerate
    # check the 4 corners (P is convex in (X,Y): linear constraints) -> corners suffice
    for X in (xlo, xhi):
        for Y in (ylo, yhi):
            if not in_P(X, Y, p, p2, q, r, s):
                return False
    return True

def Rp_has_witness(p, p2, q, r, s):
    xlo, xhi, ylo, yhi = Rp_bounds(q, r, s)
    pts = []
    for l in range(q):
        X, Y = S(l, p, q, r)
        if xlo <= X <= xhi and ylo <= Y <= yhi:
            pts.append((l, X, Y))
    return pts

for (ii, jj) in [(1, 2), (1, -2)]:
    survs = survivors(ii, jj, 60)
    binv = check_invariant(ii, jj, survs)
    print(f"\n=== pair ({ii},{jj}): {len(survs)} survivors (q<61) ===")
    print(f"  Q1 invariant ({jj}X - Y const mod1): violations = {binv}/{len(survs)}")
    deg = subP_fail = noRpwit = 0
    cmp_tot = 0
    Rp_widths = []
    Rp_mincount = []
    for (p, q, r) in survs:
        for p2 in range(p + 1, q):
            for s in range(r + 1, 3 * q + 1):
                cmp_tot += 1
                sub = Rp_subset_P(p, p2, q, r, s)
                if sub is None:
                    deg += 1
                    continue
                if sub is False:
                    subP_fail += 1
                pts = Rp_has_witness(p, p2, q, r, s)
                if not pts:
                    noRpwit += 1
                else:
                    Rp_mincount.append(len(pts))
                xlo, xhi, _, _ = Rp_bounds(q, r, s)
                Rp_widths.append(float(xhi - xlo))
    print(f"  Q2a Rp ⊆ P fails:        {subP_fail}/{cmp_tot}")
    print(f"  Q2b Rp degenerate (xhi<xlo): {deg}/{cmp_tot}")
    print(f"  Q2b Rp has NO witness:   {noRpwit}/{cmp_tot}")
    if Rp_mincount:
        print(f"  Rp witness count: min={min(Rp_mincount)} mean={sum(Rp_mincount)/len(Rp_mincount):.1f}")
    if Rp_widths:
        print(f"  Rp X-width: min={min(Rp_widths):.4f} mean={sum(Rp_widths)/len(Rp_widths):.4f}")
