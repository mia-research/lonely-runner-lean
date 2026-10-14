#!/usr/bin/env python3
"""RIGID-class sweep, executed to docs/n8/PREREG_RIGID_CLASS_v1.md.

Primary statistic K = number of frame tuples satisfying C1 and C2 that are NOT RIGID,
per n, reported with the explicit falsifier list.  Also M1/M2 (RIGID tuples violating
C1 / C2), the full 2x2, and the prereg's structure log.

Frame: T an (n-1)-subset of [1, 4n] INCLUSIVE.  (PART 4 of exact_phi_n_ap_v1.py used
[1, 4n-1]; a different frame -- counts must not be merged.)

Exactness: fractions.Fraction throughout the signal path; no float, no tolerance.
lonely_set is REUSED unmodified from exact_phi_n_ap_v1.py, pinned by SHA-256.
"""
import sys, os, io, json, hashlib, random, contextlib
from fractions import Fraction as F
from math import gcd
from itertools import combinations
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
MODULE = os.path.join(HERE, "exact_phi_n_ap_v1.py")
SHA_PINNED = "fb08b8cbba3d7f3ecc743fbcfef1b550e75082023ace1f2ae67e8f86a5c7850d"

_sha = hashlib.sha256(open(MODULE, "rb").read()).hexdigest()
assert _sha == SHA_PINNED, f"module changed: {_sha} != {SHA_PINNED}"

sys.path.insert(0, HERE)
with contextlib.redirect_stdout(io.StringIO()):      # module has no __main__ guard
    from exact_phi_n_ap_v1 import lonely_set          # noqa: E402

SEED = 8081729

# ---------------------------------------------------------------- predicates
def units(n):        return {u for u in range(1, n) if gcd(u, n) == 1}
def C1(T, n):        return units(n) <= {v % n for v in T}
def C2(T, n):        return all(any(v % q == 0 for v in T) for q in range(2, n))
def want_pts(n):     return [F(r, n) for r in range(1, n) if gcd(r, n) == 1]

def _norm(x):
    assert isinstance(x, F), f"float breach on signal path: {type(x)}"
    r = x - (x.numerator // x.denominator)
    return min(r, 1 - r)

def analyse(T, n):
    """Exact (rigid, isolated_pts, intervals), with an independent re-verification
    of every isolated point using a Fraction-only predicate."""
    pts, ivs = lonely_set(list(T), n)
    b = F(1, n)
    for p in pts:                                     # exactness assertion, inner loop
        assert isinstance(p, F)
        assert all(_norm(p * v) >= b for v in T), f"lonely_set returned a non-lonely point {p}"
    for a, c in ivs:
        assert isinstance(a, F) and isinstance(c, F)
    rigid = (not ivs) and sorted(pts) == want_pts(n)
    return rigid, sorted(pts), ivs

def structure(T, n, pts, ivs):
    w = set(want_pts(n))
    p = set(pts)
    return {
        "T": list(T),
        "missing_points":  [str(x) for x in sorted(w - p)],
        "extra_points":    [str(x) for x in sorted(p - w)],
        "n_points_surviving": len(w & p),
        "intervals":       [[str(a), str(c)] for a, c in ivs],
        "failing_q":       [q for q in range(2, n) if not any(v % q == 0 for v in T)],
        "uncovered_units": sorted(units(n) - {v % n for v in T}),
    }

# ---------------------------------------------------------------- controls
def firing_controls():
    print("=" * 78)
    print("FIRING CONTROLS (prereg sec 4) -- both directions, abort on failure")
    print("=" * 78)
    ok = True

    T, n = [1, 3, 5, 7, 9, 11, 13], 8
    rigid, pts, ivs = analyse(T, n)
    half = [(a, c) for a, c in ivs if a <= F(1, 2) <= c]
    passed = (not rigid) and len(half) >= 1
    print(f"[1] not-rigid  T={T} n={n}")
    print(f"    C1={C1(T,n)}  C2={C2(T,n)}  failing q={[q for q in range(2,n) if not any(v%q==0 for v in T)]}")
    print(f"    RIGID={rigid}  isolated={[str(x) for x in pts]}  components={len(ivs)}")
    for a, c in ivs:
        print(f"      [{a}, {c}]" + ("   <-- contains 1/2" if a <= F(1,2) <= c else ""))
    print(f"    PASS (RIGID=False and an interval contains 1/2): {passed}")
    print(f"    owner stated 5 components; run prints {len(ivs)} -> "
          f"{'agrees' if len(ivs)==5 else 'DISCLOSED DISCREPANCY against owner figure'}")
    ok &= passed

    print(f"[2] rigid-must-fire")
    for T, n in [([1,2,3,4,5,6,7], 8), ([1,2,3,4,5,7,12], 8), ([1,3,4,7], 5)]:
        rigid, pts, ivs = analyse(T, n)
        p = rigid and len(pts) == len(want_pts(n)) and not ivs
        print(f"    T={T} n={n}: RIGID={rigid} pts={len(pts)}/{len(want_pts(n))} ivs={len(ivs)}  PASS={p}")
        ok &= p
    return ok

def planted_controls(rng):
    print("=" * 78)
    print("PLANTED CONTROLS (prereg sec 4) -- forced effect, must fire 100%")
    print("=" * 78)
    ok = True
    print("(a) all-odd tuples: ||v/2||=1/2 >= 1/n forced, so a component containing 1/2 is forced")
    for n in range(4, 13):
        odds = [x for x in range(1, 4 * n + 1) if x % 2 == 1]
        fired = 0
        for _ in range(20):
            T = sorted(rng.sample(odds, n - 1))
            rigid, pts, ivs = analyse(T, n)
            if (not rigid) and any(a <= F(1, 2) <= c for a, c in ivs):
                fired += 1
        print(f"    n={n:>2}: {fired}/20" + ("" if fired == 20 else "   <-- PLANT MISFIRE"))
        ok &= (fired == 20)

    print("(b) C2 satisfied, one unit residue u omitted: a point r/n must be missing or non-isolated")
    for n in range(4, 13):
        fired = tries = 0
        while fired + (20 - fired) > 0 and tries < 4000 and fired < 20:
            tries += 1
            u = rng.choice(sorted(units(n)))
            pool = [x for x in range(1, 4 * n + 1) if x % n != u]
            S = set()
            bad = False
            for q in range(2, n):
                if any(v % q == 0 for v in S):
                    continue
                cands = [m for m in pool if m % q == 0 and m not in S]
                if not cands:
                    bad = True; break
                S.add(rng.choice(cands))
            if bad or len(S) > n - 1:
                continue
            rest = [x for x in pool if x not in S]
            if len(rest) < n - 1 - len(S):
                continue
            S |= set(rng.sample(rest, n - 1 - len(S)))
            T = sorted(S)
            if not C2(T, n) or u in {v % n for v in T}:
                continue
            rigid, pts, ivs = analyse(T, n)
            if not rigid:
                fired += 1
        print(f"    n={n:>2}: {fired}/20 (draws {tries})" + ("" if fired == 20 else "   <-- PLANT MISFIRE"))
        ok &= (fired == 20)
    return ok

# ---------------------------------------------------------------- arms
def _cell(T, n):
    both = C1(T, n) and C2(T, n)
    rigid, pts, ivs = analyse(T, n)
    return both, rigid, pts, ivs

def _exh_chunk(args):
    n, first = args
    hi = 4 * n
    res = {"both_rigid": 0, "both_not": 0, "not_rigid": 0, "not_not": 0,
           "K_list": [], "M_list": [], "surv": {}}
    for rest in combinations(range(first + 1, hi + 1), n - 2):
        T = (first,) + rest
        c1, c2 = C1(T, n), C2(T, n)
        both = c1 and c2
        rigid, pts, ivs = analyse(T, n)
        if both and rigid:      res["both_rigid"] += 1
        elif both and not rigid:
            res["both_not"] += 1
            res["K_list"].append(structure(T, n, pts, ivs))
        elif rigid:
            res["not_rigid"] += 1
            res["M_list"].append(structure(T, n, pts, ivs))
        else:                   res["not_not"] += 1
        if (c1 ^ c2):           # near-miss arm: how many phi(n) points survive
            k = str(len(set(pts) & set(want_pts(n))))
            res["surv"][k] = res["surv"].get(k, 0) + 1
    return res

def exhaustive(n, pool):
    hi = 4 * n
    tot = 0
    agg = {"both_rigid": 0, "both_not": 0, "not_rigid": 0, "not_not": 0,
           "K_list": [], "M_list": [], "surv": {}}
    jobs = [(n, f) for f in range(1, hi - (n - 3))]
    for r in pool.imap_unordered(_exh_chunk, jobs):
        for k in ("both_rigid", "both_not", "not_rigid", "not_not"):
            agg[k] += r[k]
        agg["K_list"] += r["K_list"]; agg["M_list"] += r["M_list"]
        for k, v in r["surv"].items():
            agg["surv"][k] = agg["surv"].get(k, 0) + v
    tot = sum(agg[k] for k in ("both_rigid", "both_not", "not_rigid", "not_not"))
    return agg, tot

if __name__ == "__main__":
    stage = sys.argv[1] if len(sys.argv) > 1 else "controls"
    print(f"module SHA-256 pinned OK: {SHA_PINNED}")
    if stage == "controls":
        rng = random.Random(SEED)
        a = firing_controls()
        b = planted_controls(rng)
        print("=" * 78)
        print(f"CONTROLS: firing={'PASS' if a else 'FAIL'}  planted={'PASS' if b else 'FAIL'}")
        print("SWEEP IS VOID unless both PASS (prereg sec 7)." if not (a and b) else
              "Controls clear; exhaustive arms may run.")
    else:
        ns = [int(x) for x in sys.argv[2:]] or [4, 5, 6, 7]
        out = {}
        with Pool(10) as pool:
            for n in ns:
                agg, tot = exhaustive(n, pool)
                K, M = agg["both_not"], len(agg["M_list"])
                print(f"n={n:>2} frame C({4*n},{n-1})={tot}  "
                      f"2x2 [both&rigid={agg['both_rigid']} both&NOT={K} "
                      f"notboth&rigid={agg['not_rigid']} notboth&NOT={agg['not_not']}]  "
                      f"K={K}  M={M}", flush=True)
                out[n] = agg
        with open(os.path.join(HERE, f"rigid_sweep_v1_exh_{'_'.join(map(str,ns))}.json"), "w") as f:
            json.dump(out, f, indent=1)
