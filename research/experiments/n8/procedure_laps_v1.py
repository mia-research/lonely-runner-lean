"""
The owner's procedure, PROOF_CANDIDATE_v3 Steps 3-5 / OWNER_PROCEDURE_v2 section 1, with the
window NOT confined to the first lap (owner, 2026-09-14: isolation is not required in the first
cycle; the cycles keep going).

For runner i:
  Step 3  m = d_min from the two speed-neighbours.
  Step 4  u = m t.  The nearest runner is clear exactly on u in [k + 1/8, k + 7/8], lap k.
  Step 5  read the other SIX (remove exactly one copy of m): runner j is in the way only within
          1/(8 s_j) of a lap line u = q/s_j, the zones being OPEN.
BSM: boundary set = the window ends and every (8q +- 1)/(8 s_j) in the window.  Boundary points
and open cells are evaluated separately; touching zones are never merged.  '>= 1/8' inclusive.
Laps are read in order k = 0, 1, 2, ...  The time reported in a lap is its least clear point --
a reporting convention, not a demand of the construction.

Integer and rational speeds: exact Fractions; the reading of runner i has period m/g_i in u
(g_i = gcd of its differences), so if no lap within one period has a clear point that is
DECIDED.  Irrational speeds: exact Q(sqrt2) arithmetic; a stated lap cap.

Every returned time is re-checked independently from TRUE track positions frac(v_j t) --
nobody pinned.
"""
import sys, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from bsm_cycle_reading_v1 import R2

EIGHTH = F(1, 8)


def flo(x):
    return x.floor() if isinstance(x, R2) else floor(x)


def phase_clear(x):
    fr = x - flo(x)
    return EIGHTH <= fr <= 1 - EIGHTH


def six_readings(V, i):
    below = V[i] - V[i - 1] if i > 0 else None
    above = V[i + 1] - V[i] if i < len(V) - 1 else None
    m = min(x for x in (below, above) if x is not None)
    d = [V[j] - V[i] if V[j] > V[i] else V[i] - V[j] for j in range(len(V)) if j != i]
    d.remove(m)                                   # exactly one copy: six readings remain
    return m, [x / m for x in d]


def read_lap(s, k):
    """BSM reading of lap k's window.  Returns counts and the clear boundary points."""
    lo, hi = k + EIGHTH, k + 1 - EIGHTH
    B = {lo if not isinstance(s[0], R2) else R2(lo), hi if not isinstance(s[0], R2) else R2(hi)}
    lap_lines = 0
    for x in s:
        for q in range(flo(x * lo), flo(x * hi) + 1):
            L = q / x
            if lo <= L <= hi:
                lap_lines += 1
        for q in range(flo(x * lo) - 1, flo(x * hi) + 2):
            for sgn in (-1, 1):
                b = (8 * q + sgn) / (8 * x)
                if lo <= b <= hi:
                    B.add(b)
    if isinstance(s[0], R2):                     # exact order, no float key
        from functools import cmp_to_key
        B = sorted(B, key=cmp_to_key(lambda a, b: (a - b).sign()))
    else:
        B = sorted(B)
    ok = lambda u: all(phase_clear(x * u) for x in s)
    pts = [b for b in B if ok(b)]
    cells = [(a, b) for a, b in zip(B, B[1:]) if ok((a + b) / 2)]
    for a, b in cells:                             # open zones: a clear cell has clear ends
        assert ok(a) and ok(b), "BSM consistency"
    return dict(lap_lines=lap_lines, clear_points=len(pts), clear_intervals=len(cells),
                measure=sum((b - a for a, b in cells), F(0) if not isinstance(s[0], R2) else R2(0)),
                first=pts[0] if pts else None, cell_of_first=None)


def lonely_true_positions(V, i, t):
    xi = V[i] * t
    pi = xi - flo(xi)
    for j in range(len(V)):
        if j == i:
            continue
        xj = V[j] * t
        diff = (xj - flo(xj)) - pi
        diff = diff - flo(diff)
        if diff < EIGHTH or diff > 1 - EIGHTH:
            return False
    return True


def procedure(V, i, lap_cap=None):
    m, s = six_readings(V, i)
    if lap_cap is None:                            # rational: one period of the reading, decided
        allf = [F(x) for x in V]
        L = reduce(lambda a, b: a * b // gcd(a, b), [x.denominator for x in allf])
        diffs = [abs(int(x * L) - int(allf[i] * L)) for x in allf if x != allf[i]]
        g = F(reduce(gcd, diffs), L)
        laps = int(flo(F(m) / g)) + 2
    else:
        laps = lap_cap
    for k in range(laps):
        r = read_lap(s, k)
        if r["first"] is not None:
            u = r["first"]
            t = u / m
            v1 = min(V, key=lambda y: y.approx() if isinstance(y, R2) else y)
            return dict(m=m, lap=k, u=u, t=t, cycle=flo(t * v1), clear_points=r["clear_points"],
                        clear_intervals=r["clear_intervals"],
                        recheck=lonely_true_positions(V, i, t))
    return dict(m=m, lap=None, laps_read=laps, decided=lap_cap is None)


# ---------------------------------------------------------------------------------- controls
def controls():
    print("CONTROLS -- must reproduce OWNER_PROCEDURE_v2 section 2 and PROOF_CANDIDATE_v3 Step 4\n")
    rows = [("AP r1", (1,2,3,4,5,6,7,8), 0, dict(lap_lines=21, clear_points=4, clear_intervals=0), F(1,8)),
            ("AP r4", (1,2,3,4,5,6,7,8), 3, dict(lap_lines=9, clear_points=12, clear_intervals=6), F(1,8)),
            ("AP r8", (1,2,3,4,5,6,7,8), 7, dict(lap_lines=21, clear_points=4, clear_intervals=0), F(1,8)),
            ("r8->9 r1", (1,2,3,4,5,6,7,9), 0, dict(lap_lines=22, clear_points=12, clear_intervals=6), F(9,64)),
            ("r8->9 r8", (1,2,3,4,5,6,7,9), 7, dict(lap_lines=12, clear_points=2, clear_intervals=1), F(1,16)),
            ("two blocks r1", (8,9,10,11,15,16,17,18), 0, dict(lap_lines=29, clear_points=8, clear_intervals=4), F(9,56)),
            ("two blocks r4", (8,9,10,11,15,16,17,18), 3, dict(lap_lines=21, clear_points=4, clear_intervals=0), F(1,8)),
            ("two blocks r5", (8,9,10,11,15,16,17,18), 4, dict(lap_lines=21, clear_points=4, clear_intervals=0), F(1,8))]
    allok = True
    for name, V, i, want, t_want in rows:
        V = [F(v) for v in V]
        m, s = six_readings(V, i)
        r = read_lap(s, 0)
        got = {k: r[k] for k in want}
        t = r["first"] / m if r["first"] is not None else None
        ok = got == want and t == t_want
        allok &= ok
        print(f"  {name:<14} got {got}, t* = {t}   {'MATCH' if ok else 'MISMATCH, want ' + str(want) + ' ' + str(t_want)}")
    V = [F(v) for v in (4,12,29,37,101,121,176,196)]
    r = procedure(V, 3)
    ok = r["u"] == F(9, 64) and r["lap"] == 0 and r["recheck"]   # Step 4 states the LOCATION u
    allok &= ok
    print(f"  Step 4, six not five: r4 of (4,12,29,37,101,121,176,196) u* = {r['u']}, t* = {r['t']}   {'MATCH' if ok else 'MISMATCH'}")
    V = [F(v) for v in (1,31,75,97,128,160,176,225)]
    m, s = six_readings(V, 0)
    r0 = read_lap(s, 0)
    ok = r0["first"] is None
    allok &= ok
    print(f"  LAST_MILE runner at 1: clear points in lap 0 = {r0['clear_points']}   {'MATCH (none)' if ok else 'MISMATCH'}")
    print(f"\n  controls: {'ALL MATCH' if allok else 'FAILED -- run void'}\n")
    return allok


def report(name, arrangements, lap_cap=None, show=False):
    n = none = bad = later = 0
    worst = (-1, None)
    for V in arrangements:
        row = []
        for i in range(8):
            r = procedure(V, i, lap_cap)
            n += 1
            if r["lap"] is None:
                none += 1
                row.append("--")
                print(f"   NOT RETURNED within {r['laps_read']} laps ({'decided: a full period' if r['decided'] else 'cap'}):",
                      [str(x) for x in V], "runner", i + 1)
                continue
            if not r["recheck"]:
                bad += 1
                print("   RE-CHECK FAILED:", [str(x) for x in V], i + 1, r)
            if r["lap"] >= 1:
                later += 1
            if r["lap"] > worst[0]:
                worst = (r["lap"], ([str(x) for x in V], i + 1, str(r["t"]) if not isinstance(r["t"], R2) else r["t"].approx()))
            row.append(f"{r['t'] if not isinstance(r['t'], R2) else round(r['t'].approx(), 6)} (lap {r['lap']}, cycle {r['cycle']})")
        if show:
            print("  ", [str(x) for x in V])
            for i, x in enumerate(row):
                print(f"      r{i+1}: {x}")
    print(f"{name}: {n} runners | returned: {n - none} | not returned: {none} | re-check failures: {bad} "
          f"| returned beyond lap 0: {later} | furthest lap: {worst[0]} {worst[1] if worst[0] > 0 else ''}\n")


if __name__ == "__main__":
    if not controls():
        sys.exit(1)
    named = [(1,1975,5265,6910,8737,9589,11845,15135), (1,31,75,97,128,160,176,225),
             (27,45,308,678,679,799,806,979), (3,7,12,20,29,31,44,50), (4,12,29,37,101,121,176,196),
             (10,65,101,126,159,222,256,271), (8,9,10,11,15,16,17,18), (1,2,3,4,5,6,7,8),
             (1,2,3,4,5,6,15,16), (3,17,23,41,58,79,96,131)]
    report("named arrangements", [[F(v) for v in V] for V in named], show=True)

    root2 = R2(0, 1)
    irr = [[R2(1), R2(1) + root2 / 100] + [R2(k) for k in range(3, 9)]]
    rng = random.Random(7)
    while len(irr) < 25:
        V = sorted({(rng.randint(1, 60), rng.randint(0, 3), rng.randint(3, 40)) for _ in range(8)})
        W = sorted((R2(a) + R2(0, b) / c for a, b, c in V), key=lambda y: y.approx())
        if len({round(w.approx(), 12) for w in W}) == 8:
            irr.append(W)
    report("irrational speeds (Q(sqrt2), exact), cap 40 laps", irr, lap_cap=40)

    Bmax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    from itertools import combinations
    exh = [[F(v) for v in c] for c in combinations(range(1, Bmax + 1), 8) if reduce(gcd, c) == 1]
    report(f"exhaustive: 8 distinct positive integer speeds in [1,{Bmax}], gcd 1 ({len(exh)} arrangements)", exh)
    rng = random.Random(20260914)
    for hi, cnt in ((100, 1000), (1000, 200), (10000, 25)):
        report(f"random integer speeds in [1,{hi}], {cnt} arrangements",
               [[F(v) for v in sorted(rng.sample(range(1, hi + 1), 8))] for _ in range(cnt)])
    rat = []
    while len(rat) < 300:
        V = sorted({F(rng.randint(1, 80), rng.randint(1, 9)) for _ in range(8)})
        if len(V) == 8:
            rat.append(V)
    report("random rational speeds, 300 arrangements", rat)
