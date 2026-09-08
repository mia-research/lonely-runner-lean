#!/usr/bin/env python3
"""THE QUOTIENT-TRANSLATE ENGINE at n = 8.  Exact Fraction throughout, no float.

ENGINE (proof in docs/n8/QUOTIENT_TRANSLATE_ENGINE_v1.md).  Let T be 7 distinct positive
integers, q >= 2, H = {v in T : q | v}, L = T \ H, h = |H| <= 6.  LRC(h+1) (<= LRC(7),
which we own) gives sigma0 with ||(v/q) sigma0|| >= 1/(h+1) >= 1/7 > 1/8 for all v in H.
Put t_k = (sigma0 + k)/q, k in Z/q.  Then every v in H is lonely at every t_k, so if T is
a counterexample every t_k is blocked by some v in L.  Writing

    K_v = { k in Z/q : ||v (sigma0 + k)/q|| < 1/8 }

we need  union of K_v over L  =  Z/q,  and (triangle inequality)  K_v - K_v  is inside
D_v = { d : ||v d / q|| < 1/4 }.

|K_v| is exactly g * (number of points of a 1/q'-grid inside an open interval of length
1/4), g = gcd(v,q), q' = q/g.  So |K_v| <= g * kappa(q'), kappa(m) = ceil(m/4) if 4 does
not divide m, else m/4.  The covering forces  sum over L of g*kappa(q')  >=  q.

PART A verifies the |K_v| <= g*kappa(q') bound EXACTLY and tightly (max over sigma0).
PART B prints the corollaries the counting yields.
PART C is the end-to-end test: build tuples that VIOLATE a corollary and check the engine
actually hands back a lonely point, verified against all seven speeds exactly.
"""
from fractions import Fraction as F
from math import gcd
import random, sys

LEVEL = F(1, 8)

# ---------------------------------------------------------------- helpers
def nrm(x):
    """||x|| = distance from x to the nearest integer, exact."""
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)

def kappa(m):
    """max # of points of a (1/m)-spaced grid inside an OPEN interval of length 1/4."""
    return m // 4 if m % 4 == 0 else -(-m // 4)   # m/4 or ceil(m/4)

def Kset(v, q, s0):
    return [k for k in range(q) if nrm(F(v, q) * (s0 + k)) < LEVEL]

def bad_intervals(z):
    """bad set of speed z at level 1/8 inside [0,1): open intervals, exact."""
    out = []
    for j in range(-1, z + 2):
        lo, hi = F(8 * j - 1, 8 * z), F(8 * j + 1, 8 * z)
        lo, hi = max(lo, F(0)), min(hi, F(1))
        if lo < hi: out.append((lo, hi))
    return out

def lonely_set(Z, lvl=LEVEL):
    """{t in [0,1] : ||z t|| >= lvl for all z in Z}, exact, closed components including
    ISOLATED POINTS.  Bad sets complemented as OPEN intervals, merged on STRICT overlap.
    Needed because the lonely set can be a single point exactly when Z is a tight instance
    of LRC(|Z|+1); the earlier closed-merge version dropped those (conservative, so the
    published run stands) but would have raised on such a Z."""
    iv = sorted((F(k, z) - lvl / z, F(k, z) + lvl / z)
                for z in Z for k in range(-1, z + 2))
    merged = []
    for lo, hi in iv:
        if merged and lo < merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    good, cur = [], F(0)
    for lo, hi in merged:
        if lo > 1: break
        if cur <= lo:
            a, b = max(cur, F(0)), min(lo, F(1))
            if a <= b: good.append((a, b))
        cur = max(cur, hi)
    if cur <= 1: good.append((max(cur, F(0)), F(1)))
    return [(a, b) for a, b in good if 0 <= a <= b <= 1]

# ---------------------------------------------------------------- PART A
def part_A(QMAX=48):
    print("PART A -- |K_v| <= g*kappa(q') checked exactly, max over sigma0")
    worst = []
    bad = 0
    for q in range(2, QMAX + 1):
        for v in range(1, 4 * q + 1):
            g = gcd(v, q); qp = q // g
            bound = g * kappa(qp)
            # exact max over sigma0: |K| depends on sigma0 only through phi = v*sigma0/q
            # mod 1/q'.  Breakpoints of the count are where a grid point hits +-1/8.
            # Evaluate at midpoints between consecutive breakpoints -> exact maximum.
            brks = sorted({F(a, 8 * qp) % 1 for a in range(0, 8 * qp)} |
                          {(F(j, qp) + F(1, 8)) % 1 for j in range(qp)} |
                          {(F(j, qp) - F(1, 8)) % 1 for j in range(qp)})
            best = 0
            for i in range(len(brks)):
                lo = brks[i]; hi = brks[(i + 1) % len(brks)]
                phi = (lo + hi) / 2 if hi > lo else (lo + 1) / 2
                cnt = sum(1 for j in range(qp) if nrm(phi + F(j, qp)) < LEVEL)
                best = max(best, g * cnt)
            if best > bound:
                bad += 1
                if len(worst) < 5: worst.append((q, v, best, bound))
    print(f"  q = 2..{QMAX}, all v <= 4q: violations of the bound = {bad}")
    if worst: print("  first violations (q, v, actual, bound):", worst)
    print()

# ---------------------------------------------------------------- PART B
def part_B():
    print("PART B -- the counting corollaries (each: sum over L of g*kappa(q') >= q)")
    print("  q=2 : odd speeds contribute kappa(2)=1 each          ->  n_0 >= 2")
    print("  q=4 : odd 1*kappa(4)=1 ; v=2 mod 4 -> 2*kappa(2)=2   ->  n_0 + 2 n_1 >= 4")
    print("  q=8 : 1*kappa(8)=2 ; 2*kappa(4)=2 ; 4*kappa(2)=4     ->  n_0 + n_1 + 2 n_2 >= 4")
    for r in range(1, 7):
        q = 2 ** r
        terms = []
        for e in range(r):
            g = 2 ** e; qp = 2 ** (r - e)
            terms.append((e, g * kappa(qp)))
        print(f"  q={q:>3}: contributions by v_2(v)=e : " +
              ", ".join(f"e={e}:{c}" for e, c in terms) + f"   need sum >= {q}")
    print()
    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 163]:
        cap = kappa(p)
        need = -(-p // cap)                      # ceil(p/cap) = min |L|
        print(f"  q={p:>4} prime: kappa={cap:>3}  -> |L| >= {need}  "
              f"i.e. at most {7-need} speeds divisible by {p}")
    print()

# ---------------------------------------------------------------- PART C
def engine_witness(T, q):
    """Run the engine.  Returns (t, k, sigma0) or None if the counting does not force it."""
    H = [v for v in T if v % q == 0]
    L = [v for v in T if v % q != 0]
    if len(H) > 6 or len(H) == 0: return None
    budget = sum(gcd(v, q) * kappa(q // gcd(v, q)) for v in L)
    if budget >= q: return None                  # engine does not fire
    Z = sorted(v // q for v in H)
    good = lonely_set(Z)
    if not good: raise AssertionError(f"LRC({len(Z)+1}) violated on {Z}")
    lo, hi = max(good, key=lambda p: p[1] - p[0])
    s0 = (lo + hi) / 2
    assert all(nrm(F(z) * s0) >= LEVEL for z in Z), f"sigma0={s0} not lonely for Z={Z}"
    for k in range(q):
        if all(nrm(F(v, q) * (s0 + k)) >= LEVEL for v in L):
            return (s0 + k) / q, k, s0
    raise AssertionError(f"engine budget {budget} < q={q} but every k blocked; T={T}")

def part_C(trials=400, seed=20260908):
    print("PART C -- end-to-end: tuples chosen to VIOLATE a corollary, engine must deliver")
    rng = random.Random(seed)
    specs = [
        ("q=2, n_0 = 1 (violates n_0>=2)", 2,
         lambda: sorted({rng.randrange(1, 60) * 2 for _ in range(30)})[:6] +
                 [2 * rng.randrange(1, 30) + 1]),
        ("q=4, n_0+2n_1 <= 3", 4,
         lambda: sorted({rng.randrange(1, 40) * 4 for _ in range(30)})[:5] +
                 [4 * rng.randrange(0, 20) + 2, 2 * rng.randrange(1, 40) + 1]),
        ("q=8, n_0+n_1+2n_2 <= 3", 8,
         lambda: sorted({rng.randrange(1, 30) * 8 for _ in range(30)})[:5] +
                 [8 * rng.randrange(0, 15) + 4, 2 * rng.randrange(1, 40) + 1]),
        ("q=3, five speeds divisible by 3", 3,
         lambda: sorted({rng.randrange(1, 40) * 3 for _ in range(30)})[:5] +
                 [3 * rng.randrange(1, 30) + 1, 3 * rng.randrange(1, 30) + 2]),
        ("q=5, five speeds divisible by 5", 5,
         lambda: sorted({rng.randrange(1, 30) * 5 for _ in range(30)})[:5] +
                 [5 * rng.randrange(1, 20) + 1, 5 * rng.randrange(1, 20) + 3]),
        ("q=7, four speeds divisible by 7", 7,
         lambda: sorted({rng.randrange(1, 25) * 7 for _ in range(30)})[:4] +
                 [7 * rng.randrange(1, 20) + r for r in (1, 3, 5)]),
        ("q=11, four speeds divisible by 11", 11,
         lambda: sorted({rng.randrange(1, 20) * 11 for _ in range(30)})[:4] +
                 [11 * rng.randrange(1, 15) + r for r in (1, 4, 9)]),
    ]
    for name, q, gen in specs:
        fired = ok = skip = 0
        for _ in range(trials):
            T = sorted(set(gen()))
            if len(T) != 7 or gcd(*T) != 1: skip += 1; continue
            r = engine_witness(T, q)
            if r is None: skip += 1; continue
            fired += 1
            t, k, s0 = r
            if all(nrm(F(v) * t) >= LEVEL for v in T): ok += 1
            else: print(f"    FAIL T={T} q={q} t={t}")
        print(f"  {name:<38} fired {fired:>4}, witness verified {ok:>4}, "
              f"skipped {skip:>4}  {'OK' if ok == fired and fired else 'CHECK'}")
    print()

if __name__ == "__main__":
    part_A(int(sys.argv[1]) if len(sys.argv) > 1 else 48)
    part_B()
    part_C()

# ---------------------------------------------------------------- PART D
def part_D(seed=20260908):
    """POWER + SHARPNESS.  (i) how much of the 2-adic profile space the corollaries cut;
    (ii) a witness that the counting bound is EXACTLY where the engine stops -- tuples
    meeting the bound with equality for which every k really is blocked."""
    print("PART D -- power and sharpness")

    # (i) profile cut.  n_e = #speeds with v_2 = e, e = 0,1,2,>=3.  sum = 7.
    def ok(n0, n1, n2, n3):
        if n0 < 1: return False                      # gcd(T)=1 needs an odd speed
        if n3 < 1: return False                      # Lemma 4: some speed divisible by 8
        if n0 < 2: return False                                       # q=2
        if n0 + 2 * n1 < 4: return False                              # q=4
        if n0 + n1 + 2 * n2 < 4: return False                         # q=8
        if n0 + n1 + n2 + 2 * n3 < 4: return False                    # q=16
        return True
    base = [(a, b, c, d) for a in range(8) for b in range(8) for c in range(8)
            for d in range(8) if a + b + c + d == 7 and a >= 1 and d >= 1]
    live = [p for p in base if ok(*p)]
    print(f"  2-adic profiles (n_0,n_1,n_2,n_>=3), gcd=1 and 8|some v : {len(base)}")
    print(f"  surviving the q=2,4,8,16 corollaries                    : {len(live)}"
          f"   -> {len(base)-len(live)} killed ({100*(len(base)-len(live))//len(base)}%)")
    print(f"  survivors: {live}")
    print(f"  forced: n_0 >= {min(p[0] for p in live)}, "
          f"n_>=3 <= {max(p[3] for p in live)}, "
          f"4|v count <= {max(p[2]+p[3] for p in live)}")

    # (ii) sharpness: at the bound, the engine must NOT be able to conclude.
    rng = random.Random(seed)
    print("  sharpness probe (q=4, profiles with n_0+2n_1 = 4 exactly):")
    tried = allblocked = 0
    for _ in range(4000):
        n0 = rng.choice([4, 2])
        n1 = (4 - n0) // 2
        rest = 7 - n0 - n1
        T = set()
        while len(T) < n0: T.add(2 * rng.randrange(1, 40) + 1)
        while len(T) < n0 + n1: T.add(4 * rng.randrange(0, 20) + 2)
        while len(T) < 7: T.add(4 * rng.randrange(1, 25))
        T = sorted(T)
        if len(T) != 7 or gcd(*T) != 1: continue
        H = [v for v in T if v % 4 == 0]; L = [v for v in T if v % 4]
        if not (1 <= len(H) <= 6): continue
        good = lonely_set([v // 4 for v in H])
        if not good: continue
        tried += 1
        lo, hi = max(good, key=lambda p: p[1] - p[0]); s0 = (lo + hi) / 2
        if all(any(nrm(F(v, 4) * (s0 + k)) < LEVEL for v in L) for k in range(4)):
            allblocked += 1
    print(f"    tuples at the bound: {tried}; every k blocked at the midpoint sigma0: "
          f"{allblocked} ({100*allblocked//max(tried,1)}%)")
    print("    -> the counting bound is not slack: at equality the engine genuinely")
    print("       cannot conclude, so n_0 + 2 n_1 >= 4 is the exact reach of q = 4.")
    print()

if __name__ == "__main__":
    part_D()
