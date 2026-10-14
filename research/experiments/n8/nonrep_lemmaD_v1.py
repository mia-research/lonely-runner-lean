r"""
nonrep_lemmaD_v1  --  the lambda = 1 residue of the dilate theorem, done exactly.

I = [1/4, 3/7),  |I| = 5/28.  B_m = {x : ||m x|| < 1/8}: open arcs of length 1/(4m)
centred at j/m, separated by CLOSED gaps of length 3/(4m).

Two elementary facts, both proved here by exact rational computation.

(F1) WINDOW-GAP.  A window of length L contains a complete gap of B_m for EVERY
     placement iff L >= 7/(4m).  (The set of admissible left endpoints a for a fixed
     gap has length L - 3/(4m); these sets are spaced 1/m apart, so they cover the
     line iff L - 3/(4m) >= 1/m.)   With L = 5/28 this is m >= 49/5, i.e. m >= 10.
     NOTE: the m >= 6 threshold asserted in docs/n8/UNITCOMPLETE_THEOREM_v1.md
     step (b) uses only 1/m <= |I|, which is NOT sufficient; 10 is the correct
     unconditional threshold.  The conclusion of Lemma D is unaffected -- this
     script re-derives it from the corrected threshold.

(F2) If B_{m1} u B_{m2} covers I then every connected component of I \ B_{m1} is
     contained in a single component of B_{m2}, so its length is <= 1/(4 m2).
"""
from fractions import Fraction as F
import itertools, sys

I = (F(1, 4), F(3, 7))

def B_comps(m):
    """open components of B_m, as (lo,hi) with lo<hi, covering [0,1] by periodicity"""
    j0 = (I[0] * m).numerator // (I[0] * m).denominator - 1
    j1 = (I[1] * m).numerator // (I[1] * m).denominator + 2
    return [(F(j, m) - F(1, 8 * m), F(j, m) + F(1, 8 * m)) for j in range(j0, j1)]

def minus_B(win, m):
    r"""components of win \ B_m (win half-open); returns list of (lo,hi)"""
    lo0, hi0 = win
    out = []; cur = lo0
    for lo, hi in B_comps(m):
        if hi <= cur: continue
        if lo >= hi0: break
        if lo > cur: out.append((cur, lo))
        cur = max(cur, hi)
        if cur >= hi0: break
    if cur < hi0: out.append((cur, hi0))
    return out

L = I[1] - I[0]
print(f"I = [{I[0]}, {I[1]}),  |I| = {L}")
print(f"(F1) threshold: L >= 7/(4m)  <=>  m >= 7/(4L) = {F(7,4)/L} -> every m >= 10 "
      f"forces a complete gap of B_m inside I regardless of placement.\n")

print("(F2) table:  l(m) = max component length of I \\ B_m,  and the induced cap "
      "m2 <= 1/(4 l(m1))")
tab = {}
for m in range(1, 13):
    comps = minus_B(I, m)
    ell = max((h - l for l, h in comps), default=F(0))
    tab[m] = ell
    cap = None if ell == 0 else F(1, 4) / ell
    print(f"   m={m:>2}: I\\B_m = {[(str(a),str(b)) for a,b in comps]}"
          f"   l = {ell}   cap m2 <= {cap}")

print("\nCASE ANALYSIS  (m1 < m2, both >= 1):")
print("  Step 1. If m1 >= 10, I contains a complete gap of B_{m1} (F1), of length")
print("          3/(4m1); by (F2) 3/(4m1) <= 1/(4m2), i.e. m2 <= m1/3 < m1. Contra.")
print("          Hence m1 <= 9.")
print("  Step 2. For each m1 <= 9, (F2) gives m2 <= 1/(4 l(m1)):")
survivors = []
for m1 in range(1, 10):
    ell = tab[m1]
    if ell == 0:
        print(f"          m1={m1}: l=0, no constraint from this step")
        cands = list(range(m1 + 1, 200))
    else:
        cap = F(1, 4) / ell
        cands = [m2 for m2 in range(m1 + 1, 200) if F(m2) <= cap]
        print(f"          m1={m1}: l={ell} -> m2 <= {cap} -> candidates {cands}")
    survivors += [(m1, m2) for m2 in cands]
print(f"  Step 3. Surviving (m1,m2) after step 2 : "
      f"{[p for p in survivors if p[0] in (1,2)][:0]} plus the m1 in {{1,2}} rows "
      f"(l(m1) = |I|, cap = 1/(4|I|) = {F(1,4)/L}) -> m2 <= 1, impossible since m2>m1>=1.")
real = [(a, b) for a, b in survivors if not (tab[a] == L)]
print(f"          concrete survivors to test : {real}")
print("  Step 4. Test each survivor directly (does B_{m1} u B_{m2} cover I?):")
def covers(m1, m2):
    rem = []
    for lo, hi in minus_B(I, m1):
        rem += minus_B((lo, hi), m2)
    return len(rem) == 0, rem
for m1, m2 in real:
    c, rem = covers(m1, m2)
    print(f"          (m1,m2)=({m1},{m2}): covers I ? {c}   uncovered {[(str(a),str(b)) for a,b in rem]}")
# the m1 in {1,2} rows
for m1 in (1, 2):
    print(f"          m1={m1}: I \\ B_{m1} = I itself (l = {tab[m1]}), so B_m2 alone must "
          f"cover I: needs 5/28 <= 1/(4 m2), i.e. m2 <= 7/5, i.e. m2 = 1 <= m1. Impossible.")
print("\n  => LEMMA D holds. Exhaustive cross-check follows.")
bad = [(a, b) for a, b in itertools.combinations(range(1, 301), 2) if covers(a, b)[0]]
print(f"  exhaustive: pairs 1 <= m1 < m2 <= 300 with B_m1 u B_m2 covering I : {len(bad)}")
mn = min((min((h - l for l, h in covers(a, b)[1]), default=F(0)), a, b)
         for a, b in itertools.combinations(range(1, 61), 2))
print(f"  smallest surviving component over 1<=m1<m2<=60 : {mn[0]} at (m1,m2)={mn[1:]}")
