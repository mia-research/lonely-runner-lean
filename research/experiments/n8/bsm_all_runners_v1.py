"""
Every runner of every arrangement, by the owner's BSM exactly as on file:
bsm_first and clear are imported UNCHANGED from ok_first_iso_time_v1.py
(phi_law_paper_v2 §2.2, Algorithm 2.1).  Nothing here re-implements the method.

Reported per runner: the isolation time in original units, which cycle of the slowest
runner it falls in (floor(t * v1)), and an independent re-check of all seven distances.
'None' from bsm_first = no isolation instant in a full period of the runner's reading.
"""
import io, sys, contextlib, random, hashlib
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce

with contextlib.redirect_stdout(io.StringIO()):          # the source file prints a demo table on import
    import ok_first_iso_time_v1 as src
bsm_first, clear = src.bsm_first, src.clear
print("source ok_first_iso_time_v1.py sha256",
      hashlib.sha256(open("ok_first_iso_time_v1.py", "rb").read()).hexdigest()[:16])

def cd(x):
    f = x % 1
    return min(f, 1 - f)

def run(V):
    V = [F(v) for v in V]
    E, q = clear(V)
    v1 = min(V)
    out = []
    for i in range(len(V)):
        D = sorted({abs(w - E[i]) for w in E if w != E[i]})
        f = bsm_first(D)
        if f is None:
            out.append((i, None, None, None)); continue
        t = f * q
        ok = all(cd((V[j] - V[i]) * t) >= F(1, 8) for j in range(len(V)) if j != i)
        out.append((i, t, int(t * v1), ok))
    return out

def report(name, arrangements):
    runners = none = badcheck = 0; later = 0; maxcycle = (0, None)
    for V in arrangements:
        for i, t, cyc, ok in run(V):
            runners += 1
            if t is None:
                none += 1; print("   NO ISOLATION IN A FULL PERIOD:", V, "runner", i + 1); continue
            if not ok:
                badcheck += 1; print("   RE-CHECK FAILED:", V, "runner", i + 1, t)
            if cyc >= 1: later += 1
            if cyc > maxcycle[0]: maxcycle = (cyc, (V, i + 1, t))
    print(f"{name}: {runners} runners | no isolation time: {none} | re-check failures: {badcheck} "
          f"| time beyond the slowest runner's first cycle: {later} | furthest cycle: {maxcycle[0]}"
          + (f" at {maxcycle[1]}" if maxcycle[1] else ""))

named = [(1,1975,5265,6910,8737,9589,11845,15135), (1,31,75,97,128,160,176,225),
         (27,45,308,678,679,799,806,979), (3,7,12,20,29,31,44,50), (4,12,29,37,101,121,176,196),
         (10,65,101,126,159,222,256,271), (8,9,10,11,15,16,17,18), (1,2,3,4,5,6,7,8),
         (1,2,3,4,5,6,15,16), (3,17,23,41,58,79,96,131)]
print("\nNamed arrangements, runner by runner:")
for V in named:
    r = run(V)
    print("  ", V, "->", ["--" if t is None else str(t) for _, t, _, _ in r])
report("named", named)

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    exh = [c for c in combinations(range(1, B + 1), 8) if reduce(gcd, c) == 1]
    report(f"exhaustive, 8 distinct positive integers in [1,{B}], gcd 1 ({len(exh)} arrangements)", exh)
    rng = random.Random(20260914)
    for hi, n in ((100, 1000), (1000, 300), (10000, 60)):
        report(f"random, speeds in [1,{hi}], {n} arrangements",
               [tuple(sorted(rng.sample(range(1, hi + 1), 8))) for _ in range(n)])
    rat = [tuple(sorted({F(rng.randint(1, 60), rng.randint(1, 7)) for _ in range(8)})) for _ in range(400)]
    rat = [V for V in rat if len(V) == 8]
    report(f"random rational speeds ({len(rat)} arrangements)", rat)
