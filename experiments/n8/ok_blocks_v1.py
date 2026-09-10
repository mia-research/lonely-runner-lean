#!/usr/bin/env python3
"""THE BLOCK LEMMA at n=8, from the tiling |I| = 1/4.  Exact Fraction, no float.

I = (-1/8, 1/8) has length EXACTLY 1/4, so its translates by 1/4 TILE the circle.  Under
the shift t -> t + j/8 (j in Z/8, the r-freedom of the bridge) runner e's argument moves by
e/8, whose order in R/Z is 8, 4, 2, 1 according as v2(e) = 0, 1, 2, >=3.  Intersecting the
orbit with I and using the tiling gives EXACT counts, not bounds:

  v2=0 : orbit 8 pts spacing 1/8 -> exactly 2 blocked j (one odd, one even)
  v2=1 : orbit 4 pts spacing 1/4 -> exactly 1 orbit pt in I  =>  blocked = {j0, j0+4}
  v2=2 : orbit 2 pts spacing 1/2 -> 0 or 1                   =>  a whole parity class or 0
  v2>=3: orbit 1 pt                                          =>  all 8 or 0

So the natural unit is the BLOCK: the four classes mod 4,
    A={1,5}  B={3,7}   (odd blocks)      C={0,4}  D={2,6}   (even blocks)
A v2=1 runner covers one WHOLE block; a v2=0 runner covers ONE ELEMENT of an odd block and
ONE ELEMENT of an even block; v2=2 covers two blocks of a parity or none; v2>=3 all or none.

CRITERION (no measure anywhere).  Let u_O, u_E be the numbers of odd/even blocks NOT fully
covered by the v2>=1 runners at t.  Finishing an uncovered block needs TWO odd runners, so

        a < 2*max(u_O, u_E)   =>   X(t) > 0,  a witness exists.

PART A verifies the four orbit counts and the block shapes exactly.
PART B verifies the analytic form of the block: a v2=1 runner sits on an ODD block iff
       ||2et|| > 1/4  (and a v2=2 runner fires at all iff ||2et|| < 1/4).
PART C verifies the CRITERION implies X(t) > 0 -- the only thing that matters.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import random, sys

def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)

def v2(e):
    k = 0
    while e % 2 == 0: e //= 2; k += 1
    return k

def blocked(e, t):
    """{ j in Z/8 : runner e is bad at t + j/8 }, exact."""
    return frozenset(j for j in range(8) if nrm(F(e) * (t + F(j, 8))) < F(1, 8))

BLOCKS = {0: (0, 4), 1: (1, 5), 2: (2, 6), 3: (3, 7)}     # keyed by residue mod 4
ODD_BLOCKS, EVEN_BLOCKS = (1, 3), (0, 2)

def part_A(trials=4000, seed=20260910):
    rng = random.Random(seed)
    print("PART A -- the four orbit counts and the block shapes, exact")
    bad = {0: 0, 1: 0, 2: 0, 3: 0}
    seen = {0: set(), 1: set(), 2: set(), 3: set()}
    for _ in range(trials):
        e = rng.randrange(1, 400)
        t = F(rng.randrange(0, 9973), 9973)
        S = blocked(e, t)
        k = min(v2(e), 3)
        seen[k].add(len(S))
        if k == 0:
            ok = len(S) == 2 and len({j % 2 for j in S}) == 2
        elif k == 1:
            ok = len(S) == 2 and (max(S) - min(S)) == 4
        elif k == 2:
            ok = S == frozenset() or S == frozenset(range(0, 8, 2)) or S == frozenset(range(1, 8, 2))
        else:
            ok = S == frozenset() or len(S) == 8
        if not ok:
            bad[k] += 1
            if bad[k] < 3: print(f"    MISMATCH v2={k} e={e} t={t} S={sorted(S)}")
    for k in range(4):
        print(f"  v2={k if k<3 else '>=3'} : sizes seen {sorted(seen[k])}, shape violations {bad[k]}")
    print()
    return sum(bad.values())

def part_B(trials=4000, seed=20260910):
    rng = random.Random(seed + 1)
    print("PART B -- the analytic form of the block")
    m1 = m2 = n1 = n2 = 0
    for _ in range(trials):
        t = F(rng.randrange(0, 9973), 9973)
        e = 2 * (2 * rng.randrange(0, 200) + 1)                  # v2 = 1
        S = blocked(e, t)
        if S:
            n1 += 1
            odd_block = (min(S) % 2 == 1)
            if odd_block != (nrm(2 * F(e) * t) > F(1, 4)): m1 += 1
        e = 4 * (2 * rng.randrange(0, 200) + 1)                  # v2 = 2
        S = blocked(e, t)
        n2 += 1
        if bool(S) != (nrm(2 * F(e) * t) < F(1, 4)): m2 += 1
    print(f"  v2=1 : 'block is odd  <=>  ||2et|| > 1/4'   mismatches {m1} / {n1}")
    print(f"  v2=2 : 'runner fires  <=>  ||2et|| < 1/4'   mismatches {m2} / {n2}")
    print()
    return m1 + m2

def blocks_covered(E, t):
    """(u_O, u_E) from the v2>=1 runners only."""
    hit = set()
    for e in E:
        if v2(e) >= 1: hit |= blocked(e, t)
    full = {r for r in range(4) if set(BLOCKS[r]) <= hit}
    return (sum(1 for r in ODD_BLOCKS if r not in full),
            sum(1 for r in EVEN_BLOCKS if r not in full))

def part_C(box=16, seed=20260910):
    print("PART C -- the criterion  a < 2*max(u_O,u_E)  =>  X(t) > 0")
    rng = random.Random(seed + 2)
    fired = ok = tuples_fired = 0
    tested = 0
    tuples = []
    for T in combinations(range(1, box + 1), 7):
        if reduce(gcd, T) != 1: continue
        if not any(e % 8 == 0 for e in T): continue              # Case 2
        tuples.append(T)
    rng.shuffle(tuples)
    for T in tuples[:400]:
        tested += 1
        a = sum(1 for e in T if e % 2 == 1)
        # exact cell midpoints: every breakpoint is m/(8e)
        cuts = sorted({F(m, 8 * e) for e in T for m in range(0, 8 * e + 1)})
        any_fire = False
        for i in range(len(cuts) - 1):
            t = (cuts[i] + cuts[i + 1]) / 2
            uO, uE = blocks_covered(T, t)
            if a < 2 * max(uO, uE):
                fired += 1; any_fire = True
                allhit = set()
                for e in T: allhit |= blocked(e, t)
                if len(allhit) < 8: ok += 1
                else: print(f"    FALSIFIED T={T} t={t} uO={uO} uE={uE} a={a}")
        if any_fire: tuples_fired += 1
    print(f"  Case-2 tuples tested (box [1..{box}]) : {tested}")
    print(f"  cells where the criterion fires       : {fired}")
    print(f"  of those, X(t) > 0 actually holds     : {ok}   "
          f"{'IMPLICATION HOLDS' if ok == fired else 'FALSIFIED'}")
    print(f"  tuples the criterion settles outright : {tuples_fired} / {tested}"
          f"  ({100*tuples_fired//max(tested,1)}%)")
    print()

if __name__ == "__main__":
    b = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    part_A(); part_B(); part_C(b)

# ---------------------------------------------------------------- PART D
def part_D(trials=6000, seed=20260910):
    """THE TWO-GROUP DECOMPOSITION.

    floor(floor(8et)/2) = floor(4et), so with the quarter state q_e = floor(4et) mod 4 and
    the extra bit beta_e = floor(8et) mod 2, the blocked pair of an ODD runner e (rho = e
    mod 8) is exactly

        odd  element :  o_e = -rho*(2 q_e + 1)          mod 8      -- depends on q_e ONLY
        even element :  z_e = -2*rho*(q_e + beta_e)      mod 8      -- needs the extra bit

    The odd residues {1,3,5,7} are the KLEIN group (Z/8)^*; the even residues {0,2,4,6} are
    the CYCLIC group Z/4 under z <-> z/2.  One odd runner must cover one element of each,
    and both are driven by the SAME q_e -- but through different group structures: q -> 2q+1
    is NOT a homomorphism Z/4 -> (Z/8)^*.  That mismatch is the n=8 break-even, seen
    structurally rather than as the density identity 2*phi(8)/8 = 1."""
    rng = random.Random(seed + 3)
    print("PART D -- the two-group decomposition of an odd runner's pair")
    m0 = m1 = m2 = 0
    for _ in range(trials):
        t = F(rng.randrange(1, 9973), 9973)
        e = 2 * rng.randrange(0, 300) + 1
        S = blocked(e, t)
        o = [j for j in S if j % 2 == 1][0]
        z = [j for j in S if j % 2 == 0][0]
        rho = e % 8
        q = int(4 * F(e) * t) % 4
        beta = int(8 * F(e) * t) % 2
        if o != (-rho * (2 * q + 1)) % 8: m0 += 1
        if z != (-2 * rho * (q + beta)) % 8: m2 += 1
        chi1 = 1 if rho % 4 == 1 else -1
        eps = 1 if (2 * F(e) * t) % 1 < F(1, 2) else -1      # = (-1)^q
        if (1 if o % 4 == 1 else -1) != -chi1 * eps: m1 += 1
    print(f"  odd  element  o_e = -rho*(2q+1)      mod 8 : mismatches {m0} / {trials}")
    print(f"  even element  z_e = -2*rho*(q+beta)  mod 8 : mismatches {m2} / {trials}")
    print(f"  block of o_e  = -chi1(rho)*(-1)^q          : mismatches {m1} / {trials}"
          f"   [sign corrected: -chi1*eps, not +]")
    print()

# ---------------------------------------------------------------- PART E
def part_E(box=16, sample=400, seed=20260910):
    """WHICH SIDE CARRIES IT.  X(t) > 0 iff some residue is uncovered, i.e. the ODD side
    fails or the EVEN side fails.  The odd side is the smaller object: 4 residues, Klein
    group, driven by the quarter states q_e alone.  Measure how much of Case 2 -- and of
    the a >= 4 part the block criterion provably cannot reach -- is settled by the odd side
    on its own."""
    from collections import Counter
    rng = random.Random(seed + 4)
    tuples = [T for T in combinations(range(1, box + 1), 7)
              if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
    rng.shuffle(tuples); tuples = tuples[:sample]
    tot, odd_only, even_only, both = Counter(), Counter(), Counter(), Counter()
    for T in tuples:
        a = sum(1 for e in T if e % 2 == 1)
        tot[a] += 1
        cuts = sorted({F(m, 8 * e) for e in T for m in range(0, 8 * e + 1)})
        o_fail = e_fail = False
        for i in range(len(cuts) - 1):
            t = (cuts[i] + cuts[i + 1]) / 2
            hit = set()
            for e in T: hit |= blocked(e, t)
            if not {1, 3, 5, 7} <= hit: o_fail = True
            if not {0, 2, 4, 6} <= hit: e_fail = True
            if o_fail and e_fail: break
        if o_fail: odd_only[a] += 1
        if e_fail: even_only[a] += 1
        if o_fail and e_fail: both[a] += 1
    print(f"PART E -- which parity side yields the witness (box [1..{box}], {sample} tuples)")
    print("   a   tuples   odd side fails somewhere   even side fails somewhere   both")
    for a in sorted(tot):
        print(f"  {a:>2}   {tot[a]:>6}   {odd_only[a]:>23}   {even_only[a]:>24}"
              f"   {both[a]:>4}")
    TO, TE, TT = sum(odd_only.values()), sum(even_only.values()), sum(tot.values())
    print(f"  all  {TT:>6}   {TO:>23}   {TE:>24}   {sum(both.values()):>4}")
    print(f"  odd side alone settles {100*TO//TT}% of Case 2; "
          f"even side alone {100*TE//TT}%")
    hard = sum(tot[a] for a in tot if a >= 4)
    hardO = sum(odd_only[a] for a in odd_only if a >= 4)
    print(f"  on the a >= 4 part the block criterion cannot reach: "
          f"odd side settles {hardO} / {hard}")
    print()

if __name__ == "__main__":
    b = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    part_A(); part_B(); part_C(b); part_D(); part_E(b)
