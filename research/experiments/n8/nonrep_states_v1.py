"""
nonrep_states_v1  --  Point 1 of the non-representative brief.

The pair rule: for e = 8q + rho, bad(e,t) = {r in Z/8 : (e r + t) mod 8 in {0,7}}
depends ONLY on (rho, t mod 8), because e*r mod 8 = rho*r mod 8.

So the blocked set of the five base runners depends only on the state vector
    (t_1, t_3, t_5, t_7, t_rho0)  in  (Z/8)^5,   t_rho = floor(e_rho * x).

Enumerate all 8^5 = 32768 states for each rho0 in {2,4,6} and count how many
BLOCK (union = Z/8).  Exact integer arithmetic only.
"""
import itertools, json, sys
from collections import Counter

FULL = frozenset(range(8))

def bad(rho, t):
    return frozenset(r for r in range(8) if (rho * r + t) % 8 in (0, 7))

# sanity: pair rule for units, coset for non-units
for rho in range(1, 8):
    for q in range(0, 6):
        e = 8 * q + rho
        for t in range(64):
            direct = frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))
            assert direct == bad(rho, t % 8), (e, t)
print("[check] bad(e,t) == bad(e mod 8, t mod 8) for all e = 8q+rho, q<6, t<64 : OK")

for rho in (1, 3, 5, 7):
    for t in range(8):
        B = bad(rho, t)
        assert B == frozenset({(-t * rho) % 8, (-(t + 1) * rho) % 8}), (rho, t)
        assert len(B) == 2
        o = [r for r in B if r % 2 == 1]
        assert len(o) == 1, (rho, t, B)
print("[check] unit pair rule  bad(rho,t) = {-t*rho, -(t+1)*rho}, one odd one even : OK")

for rho in (2, 4, 6):
    for t in range(8):
        B = bad(rho, t)
        print(f"   bad({rho},{t}) = {sorted(B)}")
print()

results = {}
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    blocking = []
    uncovered_hist = Counter()
    for st in itertools.product(range(8), repeat=5):
        cov = set()
        for rho, t in zip(rhos, st):
            cov |= bad(rho, t)
        u = FULL - cov
        uncovered_hist[len(u)] += 1
        if not u:
            blocking.append(st)
    results[rho0] = blocking
    print(f"rho0 = {rho0}:  rhos = {rhos}")
    print(f"   BLOCKING states : {len(blocking)} of 32768   "
          f"= {len(blocking)}/32768 = {len(blocking)/32768:.6f}")
    print(f"   |uncovered| histogram : {dict(sorted(uncovered_hist.items()))}")
    # how many of the 4 units alone block?
    unitcov = Counter()
    for st in itertools.product(range(8), repeat=4):
        cov = set()
        for rho, t in zip((1, 3, 5, 7), st):
            cov |= bad(rho, t)
        unitcov[len(FULL - cov)] += 1
    print(f"   units {{1,3,5,7}} alone, |uncovered| histogram over 4096 states : "
          f"{dict(sorted(unitcov.items()))}")
    print()

json.dump({str(k): [list(s) for s in v] for k, v in results.items()},
          open(sys.path[0] + "/nonrep_states_v1.json", "w"))
print("blocking-state lists written to nonrep_states_v1.json")
