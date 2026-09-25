"""REDO of lap_null_v1/v2 in the framework's frame.  Exhaustive arrangements of [1,24] contain no
rule-miss runner (lap_null_arrangements_v1), and exhaustion to 41+ is ~10^8 arrangements.  So each of the
1,436 known rule-miss reading sets R (hard_sets_41_60.json) is realised as a runner INSIDE arrangements:
the runner at speed 100, the others at 100 +- r (random sides; all speeds positive and distinct, none
zero), three arrangements per R.  EVERY runner of every arrangement is evaluated with the cascade.  The
lap family / null (as lap_null_v1, 20 seeds) is run on the rule-miss runner's readings."""
import json, random, statistics as st
from collections import Counter
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
from lap_null_arrangements_v1 import lonely_open, family
H = [tuple(S) for S in json.load(open('../hard_sets_41_60.json'))]
rnd = random.Random(54); arrs = []
for R in H:
    for _ in range(3):
        V = [100] + [100 + (r if rnd.random() < 0.5 else -r) for r in R]
        arrs.append((sorted(V), 100, R))
ok = tot = 0
for V, s, R in arrs:
    assert readings(V, V.index(s)) == sorted(R)
    for k in range(8):
        t, n = cascade_cap(readings(V, k)); tot += 1; ok += t is not None
print(f"{len(arrs)} arrangements realising the 1,436 rule-miss reading sets; every runner's cascade reaches its event: {ok}/{tot}")
for Rl in (0, 1, 2):
    fams = [family(R, Rl) for R in H]
    hit = sum(any(lonely_open(R, e, j) for e, j in F_) for R, F_ in zip(H, fams))
    nulls = []
    for seed in range(20):
        r2 = random.Random(seed); c = 0
        for R, F_ in zip(H, fams):
            fl = [e for e, _ in F_]
            c += any(lonely_open(R, e, r2.randrange(e)) for e in (r2.choice(fl) for _ in F_))
        nulls.append(c)
    print(f"   rule-miss runner, laps r <= {Rl}: family {hit}/{len(H)};  null mean {st.mean(nulls):.1f} sd {st.pstdev(nulls):.1f} range {min(nulls)}-{max(nulls)}")
