"""
Isolation sets and isolation events, every runner of every arrangement.

Per runner (PROOF_CANDIDATE_v3 Steps 3-5, laps not confined to the first):
  d_min from the two neighbours; u = d_min t; read the six others lap by lap with BSM,
  window u in [k + 1/8, k + 7/8].  The first lap whose reading has clear points gives the
  runner's ISOLATION SET: its clear intervals and isolated points, exact.
Each time in the set fixes an ISOLATION EVENT: every runner's true track position at that t.

Checks, all from true positions frac(v_j t), nobody pinned:
  every isolated point, and the start, midpoint and end of every clear interval, is lonely.
Rational speeds: a runner with no clear point in one full period of its reading is DECIDED
not returned.  Irrational (Q(sqrt2), exact): lap cap stated.
"""
import sys, random
from fractions import Fraction as F
from functools import reduce, cmp_to_key
from math import gcd
from itertools import combinations
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import procedure_laps_v1 as p
from bsm_cycle_reading_v1 import R2

E8 = F(1, 8)


def lap_reading(s, k):
    isr2 = isinstance(s[0], R2)
    lo, hi = k + E8, k + 1 - E8
    B = {R2(lo), R2(hi)} if isr2 else {lo, hi}
    for x in s:
        for q in range(p.flo(x * lo) - 1, p.flo(x * hi) + 2):
            for sg in (-1, 1):
                b = (8 * q + sg) / (8 * x)
                if lo <= b <= hi:
                    B.add(b)
    B = sorted(B, key=cmp_to_key(lambda a, b: (a - b).sign())) if isr2 else sorted(B)
    ok = lambda u: all(p.phase_clear(x * u) for x in s)
    pts = [b for b in B if ok(b)]
    cells = [(a, b) for a, b in zip(B, B[1:]) if ok((a + b) / 2)]
    # merge only CLEAR cells that share an endpoint into one clear interval (that endpoint is
    # clear, so the interval is genuinely connected); in-the-way zones are never merged
    ivs = []
    for a, b in cells:
        if ivs and ivs[-1][1] == a:
            ivs[-1] = (ivs[-1][0], b)
        else:
            ivs.append((a, b))
    iso = [b for b in pts if not any(a <= b <= c for a, c in ivs)]
    return iso, ivs


def isolation_set(V, i, lap_cap=None):
    m, s = p.six_readings(V, i)
    if lap_cap is None:
        L = reduce(lambda a, b: a * b // gcd(a, b), [F(x).denominator for x in V])
        g = F(reduce(gcd, [abs(int(F(x) * L) - int(F(V[i]) * L)) for x in V if x != V[i]]), L)
        laps = int(p.flo(F(m) / g)) + 2
    else:
        laps = lap_cap
    for k in range(laps):
        iso, ivs = lap_reading(s, k)
        if iso or ivs:
            return m, k, [u / m for u in iso], [(a / m, b / m) for a, b in ivs]
    return m, None, None, None


def check_runner(args):
    V, i, lap_cap = args
    m, k, iso, ivs = isolation_set(V, i, lap_cap)
    if k is None:
        return dict(ret=False)
    events = list(iso)
    for a, b in ivs:
        events += [a, (a + b) / 2, b]
    bad = [t for t in events if not p.lonely_true_positions(V, i, t)]
    return dict(ret=True, lap=k, n_iso=len(iso), n_iv=len(ivs), n_events=len(events), bad=len(bad))


def run_family(name, arrangements, lap_cap=None, pool=None):
    jobs = [(V, i, lap_cap) for V in arrangements for i in range(8)]
    res = pool.map(check_runner, jobs, chunksize=64) if pool else list(map(check_runner, jobs))
    n = len(res)
    notret = [(jobs[j][0], jobs[j][1]) for j, r in enumerate(res) if not r["ret"]]
    got = [r for r in res if r["ret"]]
    ev = sum(r["n_events"] for r in got)
    bad = sum(r["bad"] for r in got)
    later = sum(1 for r in got if r["lap"] >= 1)
    maxlap = max((r["lap"] for r in got), default=None)
    only_points = sum(1 for r in got if r["n_iv"] == 0)
    with_point = sum(1 for r in got if r["n_iso"] > 0)
    print(f"{name}")
    print(f"   runners {n} | with an isolation set {len(got)} | not returned {len(notret)}"
          f"{' (decided, full period)' if lap_cap is None else ' (lap cap ' + str(lap_cap) + ')'}")
    print(f"   events checked {ev} | not lonely {bad}")
    print(f"   set first found beyond lap 0: {later} | furthest lap: {maxlap}")
    print(f"   sets that are isolated points only: {only_points} | sets containing an isolated point: {with_point}")
    for V, i in notret[:20]:
        print("   NOT RETURNED:", [str(x) for x in V], "runner", i + 1)
    print(flush=True)


if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    rng = random.Random(20260914)
    with Pool(8) as pool:
        exh = [[F(v) for v in c] for c in combinations(range(1, B + 1), 8) if reduce(gcd, c) == 1]
        run_family(f"exhaustive: 8 distinct positive integer speeds in [1,{B}], gcd 1, "
                   f"{len(exh)} arrangements", exh, pool=pool)
        for hi, cnt in ((100, 1000), (1000, 200), (10000, 40)):
            run_family(f"random integer speeds in [1,{hi}], {cnt} arrangements",
                       [[F(v) for v in sorted(rng.sample(range(1, hi + 1), 8))] for _ in range(cnt)],
                       pool=pool)
        rat = []
        while len(rat) < 300:
            V = sorted({F(rng.randint(1, 80), rng.randint(1, 9)) for _ in range(8)})
            if len(V) == 8:
                rat.append(V)
        run_family("random rational speeds, 300 arrangements", rat, pool=pool)
        stress = []
        for _ in range(150):                      # near-collisions among large speeds
            base = sorted(rng.sample(range(100, 5000), 7))
            j = rng.randrange(7)
            V = sorted(set(base + [base[j] + 1]))
            if len(V) == 8:
                stress.append([F(v) for v in V])
        for _ in range(150):                      # a high power of 2 against a small d_min
            a = rng.randint(1, 300)
            V = sorted({a, a + 1, a + 2 ** rng.randint(5, 9)} | set(rng.sample(range(1, 900), 5)))
            if len(V) == 8:
                stress.append([F(v) for v in V])
        run_family(f"constructed: near-collisions and powers of 2, {len(stress)} arrangements",
                   stress, pool=pool)
    root2 = R2(0, 1)
    irr = [[R2(1), R2(1) + root2 / 100] + [R2(k) for k in range(3, 9)]]
    while len(irr) < 25:
        W = sorted((R2(rng.randint(1, 60)) + R2(0, rng.randint(1, 3)) / rng.randint(3, 40)
                    for _ in range(8)), key=cmp_to_key(lambda a, b: (a - b).sign()))
        if all((W[j + 1] - W[j]).sign() > 0 for j in range(7)):
            irr.append(W)
    run_family("irrational speeds, exact Q(sqrt2), 25 arrangements", irr, lap_cap=40)
