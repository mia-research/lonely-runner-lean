#!/usr/bin/env python3
"""seven_eight_v1.py -- exact data for Task CD (Fresh/SevenEight.lean).  2026-10-10.

Exact integer / Fraction arithmetic only; no floats, no random sampling; the cascade is deterministic and every cascade
loop has a move limit (MOVE_LIMIT).  Companion C source: seven_eight_enum_v1.c (compiled and run by this script into a
temporary directory; every loop there is bounded too).

Objects (the framework's own).  A set S of positive integer disparities, m = min S, g = gcd S.  The cascade starts at
T = 8t = 1/m (R = 8 m t = 1); a state is a fraction T = num/den, R = m T.  The zone of lap k >= 1 is R in (8k-1, 8k+1)
(the unit m is in the way on all of it; its next opening is exactly R = 8k+1: Fresh.SevenEight.dmin_inWay_zone).
StrongGate_k: every cascade state in zone k moves to exactly R = 8k+1 (Fresh.SevenEight.StrongGateK).
The unit's openings are the instants R = 8k+1; the reading of d there is d(8k+1)/(8m), clear iff m <= d(8k+1) mod 8m <= 7m
(Fresh.SevenEight.not_inWay_opening_iff); the pattern is periodic in k with period m (inWay_opening_period).

Sections.
 (A) full enumerations (C): 8-subsets of {1..40} with no lonely instant; 7-subsets of {1..70} that cross R = 7; 8-subsets
     of {1..40} that cross R = 7.
 (B) populations: 7-subsets of {1..N}, N = 16, 20, 24; 8-subsets of {1..N}, N = 16, 20, 24 (gcd 1): cascade outcome
     against the strong gate at every zone entered; agreement of the cascade with the opening test.
 (C) the 47 integer 7-set gate crossers (a7 <= 70): zones, strong gate, landing, unit flank.
 (D) the endless 8-sets: period closure, the hypotheses of Fresh.SevenEight.strongGateK_of_period checked exactly, the unit
     flank (multiples of 8m), the blocked-k formula.
 (E) the unit flank over the 7- and 8-subset populations: which statements separate seven from eight.
 (F) hypothesis tests: where the smallest-disparity hypothesis of the zone lemmas is needed.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import itertools, os, subprocess, sys, tempfile, collections

MOVE_LIMIT = 20000            # no cascade loop runs longer than this many moves
HERE = os.path.dirname(os.path.abspath(__file__))


def gcdl(S):
    return reduce(gcd, S)


# ------------------------------------------------------------------------------------------------ the exact cascade
def cascade(S, limit=MOVE_LIMIT):
    """Cascade from T = 1/m.  Returns dict(S, m, g, states=[(num,den)], ended, p0, p1).  If it never fixes, the state
    repeats modulo 8/g in T (the move commutes with t -> t + 1/g since every d t shifts by d/g, an integer); then p0 < p1
    are the first repeated key (states[p1] = states[p0] + shift)."""
    S = tuple(sorted(S)); m = S[0]; g = gcdl(S)
    num, den = 1, m
    states = [(num, den)]
    seen = {}
    ended = False; p0 = p1 = None
    for it in range(limit):
        key = (num * g) % (8 * den)
        kg = gcd(key, 8 * den)
        key = (key // kg, (8 * den) // kg)
        if key in seen:
            p0 = seen[key]; p1 = it
            break
        seen[key] = it
        on = None; od = 1
        for d in S:
            x = d * num; M = 8 * den; r = x % M
            if r < den: N = (x - r) // M
            elif r > 7 * den: N = (x - r) // M + 1
            else: continue
            pn = 8 * N + 1; pd = d
            if on is None or pn * od > on * pd:
                on, od = pn, pd
        if on is None:
            ended = True
            break
        gg = gcd(on, od); num, den = on // gg, od // gg
        states.append((num, den))
    else:
        raise RuntimeError("move limit reached for %s" % (S,))
    return dict(S=S, m=m, g=g, states=states, ended=ended, p0=p0, p1=p1)


def Rof(m, st):
    return F(m * st[0], st[1])


def zone_of(R):
    """k >= 1 with R in the open zone (8k-1, 8k+1), else None."""
    k = int((R + 1) // 8)
    if k >= 1 and R + 1 > 8 * k and R < 8 * k + 1:
        return k
    return None


def zone_events(c):
    """[(n, k, R_n, R_{n+1}, strong)] for every state n having a successor in the list and lying in a zone."""
    m = c['m']; st = c['states']; ev = []
    for n in range(len(st) - 1):
        R = Rof(m, st[n]); k = zone_of(R)
        if k is not None:
            R2 = Rof(m, st[n + 1])
            ev.append((n, k, R, R2, R2 == 8 * k + 1))
    return ev


def lonely_exists(S):
    """Opening test (Localisation): some opening j of some flank e is lonely; j in 0..e-1 suffices."""
    for e in S:
        for j in range(e):
            if all(e <= (d * (8 * j + 1)) % (8 * e) <= 7 * e for d in S):
                return True
    return False


def unit_clear_k(S):
    """k in [0, m) such that the unit's opening R = 8k+1 is lonely (the unit flank alive)."""
    m = min(S)
    return [k for k in range(m) if all(m <= (e * (8 * k + 1)) % (8 * m) <= 7 * m for e in S)]


def blocked_k(S, e):
    m = min(S)
    return [k for k in range(m) if not (m <= (e * (8 * k + 1)) % (8 * m) <= 7 * m)]


def blocked_count_formula(e, m):
    """number of k in [0, m) at which e blocks the unit's opening: g * #{u in (-m', m') : u = e' (mod 8)}."""
    g = gcd(e, m); e1 = e // g; m1 = m // g
    return g * sum(1 for u in range(-m1 + 1, m1) if (u - e1) % 8 == 0)


def mults8m(S):
    m = min(S)
    return [d for d in S if d % (8 * m) == 0]


def is_grid(S):
    m = min(S)
    return all(d % m == 0 for d in S)


def landing_openers(c):
    """the elements whose opening is the landing state of an ended cascade."""
    m = c['m']; num, den = c['states'][-1]
    t = F(num, 8 * den)
    return [d for d in c['S'] if (d * t - F(1, 8)).denominator == 1]


def fr(x):
    return str(x)


# ------------------------------------------------------------------------------------------------ (A) C enumerations
def run_c(mode, K, N, workers=None):
    workers = workers or os.cpu_count() or 4
    tmp = tempfile.mkdtemp(prefix="se_")
    exe = os.path.join(tmp, "enum")
    subprocess.run(["cc", "-O2", "-o", exe, os.path.join(HERE, "seven_eight_enum_v1.c")], check=True)
    procs = [subprocess.Popen([exe, mode, str(K), str(N), str(w), str(workers)], stdout=subprocess.PIPE, text=True)
             for w in range(workers)]
    sets = []; tested = 0; flagged = 0
    for p in procs:
        out, _ = p.communicate()
        for line in out.splitlines():
            if line.startswith('#'):
                parts = line.split()
                tested += int(parts[7]); flagged += int(parts[9])
            else:
                sets.append(tuple(map(int, line.split()[1:])))
    sets.sort()
    assert flagged == len(sets)
    return sets, tested


print("seven_eight_v1.py  MOVE_LIMIT = %d" % MOVE_LIMIT)
print("=" * 118)
print("(A) full enumerations in C (exact integers)")
E8, t8 = run_c("lonely", 8, 40)
prim = [S for S in E8 if gcdl(S) == 1]
print("  8-subsets of {1..40} with NO lonely instant: tested %d subsets, found %d (gcd 1: %d; gcd > 1: %d)"
      % (t8, len(E8), len(prim), len(E8) - len(prim)))
X7, t7 = run_c("cross", 7, 70)
print("  7-subsets of {1..70}: tested %d subsets; the cascade from R = 1 passes R = 7 (a gate crosser): %d sets"
      % (t7, len(X7)))
X8, t8x = run_c("cross", 8, 40)
print("  8-subsets of {1..40}: tested %d subsets; the cascade passes R = 7: %d sets (endless: %d)"
      % (t8x, len(X8), sum(1 for S in X8 if S in set(E8))))
assert set(E8) <= set(X8)

# ------------------------------------------------------------------------------------------------ (B) populations
print("=" * 118)
print("(B) populations, gcd 1.  Per set: cascade ended / endless; zones entered (states with R in (8k-1,8k+1), k >= 1);")
print("    StrongGate_k at every zone entered; agreement of 'cascade ended' with the opening test 'a lonely instant exists'.")


def population(K, N):
    cnt = collections.Counter()
    first_bad = []
    maxj = 0
    for S in itertools.combinations(range(1, N + 1), K):
        if gcdl(S) != 1:
            continue
        c = cascade(S)
        ev = zone_events(c)
        cnt['sets'] += 1
        lon = lonely_exists(S)
        cnt['agree(ended == opening test)'] += (c['ended'] == lon)
        if c['ended'] != lon:
            first_bad.append(S)
        cnt['ended' if c['ended'] else 'endless'] += 1
        cnt['zone events'] += len(ev)
        if ev:
            cnt['sets entering a zone'] += 1
            if not all(e[4] for e in ev):
                cnt['sets with a NON-strong zone'] += 1
                first_bad.append(('nonstrong', S))
        if c['ended']:
            R = Rof(c['m'], c['states'][-1]); j = int((R - 1) // 8)
            maxj = max(maxj, j)
            zs = sorted(set(e[1] for e in ev))
            cnt['ended: zones entered == 1..j'] += (zs == list(range(1, j + 1)))
            cnt['ended: landing at R = 8j+1 exactly'] += ((R - 1) % 8 == 0 and R > 1)
            cnt['ended: landing at R = 1'] += (R == 1)
        else:
            cnt['endless: p0 = 0'] += (c['p0'] == 0)
    return cnt, first_bad, maxj


for K in (7, 8):
    for N in (16, 20, 24):
        cnt, bad, maxj = population(K, N)
        print("  K=%d (%s disparities), {1..%d}: max landing slot j over ended = %d" % (K, "seven" if K == 7 else "eight", N, maxj))
        for k in sorted(cnt):
            print("      %-44s %d" % (k, cnt[k]))
        print("      violations/bad list:", bad[:5])

# ------------------------------------------------------------------------------------------------ (C) crossers
print("=" * 118)
print("(C) the %d integer 7-set gate crossers (a7 <= 70; exact cascade).  Columns: set | m | zone events (k, R_n, R_n+1, strong)"
      " | landing R* | slot j | unit flank alive (k list) | multiples of 8m | landing openers" % len(X7))
cc = collections.Counter()
for S in X7:
    c = cascade(S)
    ev = zone_events(c)
    assert c['ended']
    R = Rof(c['m'], c['states'][-1]); j = int((R - 1) // 8)
    uk = unit_clear_k(S)
    cc['all crossers'] += 1
    cc['landing R* = 9  <=>  unit opening k = 1 alive: violations'] += ((R == 9) != (1 in uk))
    cc['all zones strong'] += all(e[4] for e in ev)
    cc['landing slot j = 1'] += (j == 1)
    cc['landing exactly R = 9'] += (R == 9)
    cc['landing > 9'] += (R > 9)
    cc['unit flank alive (some k)'] += bool(uk)
    cc['gcd 1'] += (gcdl(S) == 1)
    cc['contains a multiple of 8m'] += bool(mults8m(S))
    cc['grid (m divides every member)'] += is_grid(S)
    print("  %s | m=%d | %s | R*=%s | j=%d | unit alive k=%s | mult8m=%s | openers=%s"
          % (S, c['m'], [(e[1], fr(e[2]), fr(e[3]), e[4]) for e in ev], fr(R), j, uk, mults8m(S), landing_openers(c)))
print("  summary:", dict(cc))

# ------------------------------------------------------------------------------------------------ (D) endless sets
print("=" * 118)
print("(D) the %d endless 8-sets (a8 <= 40): period closure and the hypotheses of Fresh.SevenEight.strongGateK_of_period" % len(E8))
print("    tau = c/m is the shift of t over one period (R shifts by 8c); P = moves per period; checked exactly:")
print("    (H1) seq P = seq 0 + c/m,  (H2) every d has d*c/m an integer,  (H3) every state n < P in a zone j >= 1 moves to 8j+1.")
dd = collections.Counter()
for S in E8:
    c = cascade(S)
    m = c['m']; st = c['states']
    assert not c['ended'] and c['p0'] == 0
    P = c['p1']
    T0 = F(*st[0]); TP = F(st[P][0], st[P][1]) if P < len(st) else None
    # states list has length P+1 when the loop stopped at it == P (the repeat is computed lazily): compute state P by one move
    if TP is None:
        raise RuntimeError("period state missing")
    dT = TP - T0                       # shift in T = 8t
    tau = dT / 8                       # shift in t
    cc_ = tau * m                      # c
    H1 = (cc_.denominator == 1 and cc_ > 0)
    cint = int(cc_) if H1 else None
    H2 = H1 and all((d * cint) % m == 0 for d in S)
    H3 = True
    for n in range(P):
        R = Rof(m, st[n]); k = zone_of(R)
        if k is not None and Rof(m, st[n + 1]) != 8 * k + 1:
            H3 = False
    # d_min sets the last move of the period (the move into R = 1 + 8c): d_min in the way at state P-1 with next opening = state P
    def in_way_(d, num, den):
        r = (d * num) % (8 * den)
        return r < den or r > 7 * den
    def next_open_(d, num, den):
        x = d * num; M_ = 8 * den; r = x % M_
        N_ = (x - r) // M_ if r < den else (x - r) // M_ + 1
        return F(8 * N_ + 1, d)
    nP1 = st[P - 1]
    dminlast = in_way_(m, *nP1) and next_open_(m, *nP1) == F(*st[P])
    dd['d_min sets the last move of the period (into R = 1+8c)'] += dminlast
    dd['sets'] += 1; dd['H1 closure with integer c'] += H1; dd['H2 d*c/m integer'] += H2; dd['H3 window strong'] += H3
    dd['c = 1'] += (cint == 1)
    mu = mults8m(S)
    dd['exactly one multiple of 8m'] += (len(mu) == 1)
    dd['m = g (grid)'] += (m == c['g'])
    dd['m = 1'] += (m == 1)
    # first-zone R values
    ev = zone_events(c)
    zk = [(e[1], fr(e[2]), fr(e[3])) for e in ev if e[0] < P]
    if gcdl(S) == 1:
        print("  %s | m=%d P=%d c=%s | multiples of 8m %s | zone events in the period %s | d_min sets last move of period: %s"
              % (S, m, P, cint, mu, zk, dminlast))
print("  summary over all %d endless sets:" % len(E8), dict(dd))
print("  => by strongGateK_of_period (Lean, [L]) the hypotheses H1-H3 give StrongGate_k for EVERY k >= 1 for these sets"
      " [L conditional on the exact finite check above: OBS].")

print("  the unit flank of the endless sets: unit openings alive for some k?  ",
      sum(1 for S in E8 if unit_clear_k(S)), "of", len(E8), "(Lean: endless_has_multiple / endless_openings_blocked)")
print("  every endless set contains a multiple of 8m:", all(mults8m(S) for S in E8))
print("  residue classes of the other seven readings (e/m mod 8) for the gcd-1 endless sets:")
for S in prim:
    m = min(S); mu = mults8m(S)
    rest = [d for d in S if d not in mu]
    print("     %s  multiple(s) %s  rest mod 8 (units of m) %s" % (S, mu, sorted(((d // m) % 8) for d in rest)))

# the blocked-k formula
print("-" * 118)
print("  blocked-k formula (reasoned, e' = e/g, m' = m/g, g = gcd(e,m)): #blocked k in [0,m) = g * #{u in (-m',m'): u = e' mod 8}")
tot = bad = 0
for K, N in ((7, 20), (8, 16)):
    for S in itertools.combinations(range(1, N + 1), K):
        m = S[0]
        for e in S:
            tot += 1
            if len(blocked_k(S, e)) != blocked_count_formula(e, m):
                bad += 1
for S in X7 + X8:
    m = S[0]
    for e in S:
        tot += 1
        if len(blocked_k(S, e)) != blocked_count_formula(e, m):
            bad += 1
print("  pairs (set, e) checked: %d; mismatches: %d" % (tot, bad))

# ------------------------------------------------------------------------------------------------ (E) separation tests
print("=" * 118)
print("(E) statements about the unit's openings over the populations (gcd 1), seven readings against eight readings")
print("    U = unit flank alive (some k in [0,m) with every reading clear at R = 8k+1).  M = a member divisible by 8m.")
print("    G = m divides every member (grid).  Lean: opening_lonely_iff (G: U <=> not M), endless_has_multiple (endless, G => M).")
tab = collections.Counter()
land_mult = collections.Counter()
viol_iff = 0
for K in (7, 8):
    for N in (16, 20, 24):
        for S in itertools.combinations(range(1, N + 1), K):
            if gcdl(S) != 1:
                continue
            c = cascade(S)
            U = bool(unit_clear_k(S)); M = bool(mults8m(S)); G = is_grid(S)
            if G and (U == M):
                viol_iff += 1
            key = (K, N, 'endless' if not c['ended'] else 'ended')
            tab[key + ('U' if U else 'notU',)] += 1
            tab[key + ('M' if M else 'notM',)] += 1
            tab[key + ('G' if G else 'notG',)] += 1
            if c['ended'] and not U:
                # where the isolation goes when the unit flank is dead
                ops = landing_openers(c)
                R = Rof(c['m'], c['states'][-1])
                tab[(K, N, 'ended, unit dead')] += 1
                if M and G:
                    land_mult[(K, N, 'multiple is a landing opener' if any(o % (8 * c['m']) == 0 for o in ops) else 'multiple is NOT a landing opener')] += 1
for k in sorted(tab, key=str):
    print("   ", k, tab[k])
print("  grid sets with  U == M  (Lean says U <=> not M): violations =", viol_iff)
for k in sorted(land_mult):
    print("   ", k, land_mult[k])
print("  examples: unit flank dead, cascade ended (the isolation is displaced off the unit):")
for S in [(1, 2, 3, 4, 5, 6, 8), (1, 2, 3, 4, 5, 7, 8), (2, 3, 4, 5, 6, 7, 15), (1, 2, 3, 4, 5, 6, 24)]:
    c = cascade(S)
    print("    %s  R-states %s  landing openers %s  unit alive %s"
          % (S, [fr(Rof(c['m'], s)) for s in c['states']], landing_openers(c), unit_clear_k(S)))

# ------------------------------------------------------------------------------------------------ (F) hypothesis tests
print("=" * 118)
print("(F) hypothesis test for zone_entry / first_state_above: 'm is the LEAST element'.  Search all 3- and 4-subsets of")
print("    {1..14} and every non-least member m: a cascade from R = 1 (T = 1/m) whose state sequence jumps over the zone of")
print("    lap k (state <= (8k-1)/(8m), next state >= (8k+1)/(8m)), so no state lies in the zone.")
found = []
for K in (2, 3, 4):
    for S in itertools.combinations(range(1, 15), K):
        for m in S[1:]:
            # cascade from T = 1/m with the set S (m not least)
            num, den = 1, m
            states = [(num, den)]
            for _ in range(200):
                on = None; od = 1
                for d in S:
                    x = d * num; M_ = 8 * den; r = x % M_
                    if r < den: N_ = (x - r) // M_
                    elif r > 7 * den: N_ = (x - r) // M_ + 1
                    else: continue
                    pn = 8 * N_ + 1
                    if on is None or pn * od > on * d:
                        on, od = pn, d
                if on is None:
                    break
                g_ = gcd(on, od); num, den = on // g_, od // g_
                states.append((num, den))
            Rs = [F(m * a, b) for a, b in states]
            for n in range(len(Rs) - 1):
                for k in range(1, 6):
                    if Rs[n] <= 8 * k - 1 and Rs[n + 1] >= 8 * k + 1:
                        found.append((S, m, k, fr(Rs[n]), fr(Rs[n + 1])))
print("    first examples (set, m, k, R_n, R_n+1):", found[:6], " total found:", len(found))
print("done.")
