r"""
rt_limit_probe_v1 -- does any rank-<=2 resonance class have limit above 1/4?

rt_lattice_v1 answers this EXHAUSTIVELY for classes generated at sup-norm height <= 3
(maximum 1/4).  This script probes higher heights by random sampling, to say whether the
1/4 ceiling is an artefact of the height cut.  Sampling only; the scope of a null here is
"not found in this sample", never "does not exist".

usage:  python3 rt_limit_probe_v1.py [HMAX] [NTRIAL] [SEED]
"""
import sys, itertools, random
from fractions import Fraction as F
import rt_limit_v2 as RL

HMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8
NT = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 5

rng = random.Random(SEED)
adm = [v for v in itertools.product(range(-HMAX, HMAX + 1), repeat=4) if RL.admissible(v)]
print(f"admissible primitive resonance vectors of height <= {HMAX}: {len(adm)}")

best1 = (F(0), None)
seen = set()
n1 = 0
for v in adm:
    k, rk = RL.lattice_key([list(v)])
    if k in seen:
        continue
    seen.add(k)
    if not RL.witnesses([list(v)], PMAX=16, want=1):
        continue
    n1 += 1
    L = RL.rank1_limit(v)
    if L > best1[0]:
        best1 = (L, v)
print(f"rank-1: {n1} realisable classes tested, max limit {best1[0]} "
      f"= {float(best1[0]):.6f} at {best1[1]}")

best2 = (F(0), None)
seen2 = set()
n2 = 0
over = []
for _ in range(NT):
    a, b = rng.sample(adm, 2)
    M = [list(a), list(b)]
    B, rk = RL.kernel_basis(M)
    if rk != 2:
        continue
    k, _ = RL.lattice_key(M)
    if k in seen2:
        continue
    seen2.add(k)
    if not RL.witnesses(M, PMAX=16, want=1):
        continue
    n2 += 1
    try:
        L = RL.rank2_limit(M)
    except AssertionError:
        continue
    if L > F(1, 4):
        over.append((L, k))
    if L > best2[0]:
        best2 = (L, k)
print(f"rank-2: {n2} distinct realisable classes sampled, max limit {best2[0]} "
      f"= {float(best2[0]):.6f}")
print(f"    classes with limit > 1/4: {len(over)}")
for L, k in sorted(over, reverse=True)[:10]:
    print(f"       {k}  o_inf = {L} = {float(L):.6f}")
print(f"    classes with limit > 1/3: {sum(1 for L, k in over if L > F(1,3))}")
