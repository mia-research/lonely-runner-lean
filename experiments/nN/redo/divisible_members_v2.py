"""E406 (2026-10-06), divisible_members_v2: divisible_members_v1 made reproducible.  v1 stopped on a clock, so
its counts depend on machine speed; v2 stops after a fixed number of construction draws (A: 6,000,000 with
seed 1; B: 8,000,000 with seed 2) and stores the members in divisible_members_v2.json.  Constructions and the
residual predicate are v1's (imported, unchanged).  Recorded: the same per-member fields as v1.
"""
import sys, json, math, random, collections
from fractions import Fraction as F
sys.path.insert(0, '.')
from divisible_members_v1 import build_A, build_B, full_residual, cascade, E8

def members(build, seed, draws):
    rnd = random.Random(seed); mem = []
    for _ in range(draws):
        S = build(rnd)
        if S is None or len(S) != 7: continue
        M = [d for d in S if d % 8 == 0]; W = [d for d in S if d % 8]
        if len(M) != 3 or any(w % 2 == 0 for w in W): continue
        if not all(any((m // 8) % w == 0 for m in M) for w in W): continue
        if full_residual(S): mem.append(S)
    return list(dict.fromkeys(mem))

if __name__ == '__main__':
    out = open('divisible_members_v2.out', 'w'); out.write(__doc__ + "\n"); store = {}
    for name, build, seed, draws in (('A', build_A, 1, 6000000), ('B', build_B, 2, 8000000)):
        mem = members(build, seed, draws); store[name] = [list(S) for S in mem]
        st = collections.Counter()
        for S in mem:
            s = sorted(S); r = F(s[4], s[3])
            sep = 'ratio >= 26' if r >= 26 else ('ratio in [9, 26)' if r >= 9 else 'ratio < 9')
            t = cascade(list(S)); op = [d for d in S if d * t - math.floor(d * t) == E8]
            W = [d for d in S if d % 8]
            divided = [e for e in op if e % 8 == 0 and all((e // 8) % w == 0 for w in W)]
            kind = 'opener the divided multiple' if divided else (
                'opener another multiple of 8' if all(e % 8 == 0 for e in op) else 'opener a non-multiple')
            st[(sep, kind)] += 1
        out.write("\nconstruction %s: draws %d, members %d\n" % (name, draws, len(mem)))
        for k, v in sorted(st.items()): out.write("  %s: %d\n" % (k, v))
    json.dump(store, open('divisible_members_v2.json', 'w'))
    out.close(); print(open('divisible_members_v2.out').read()[len(__doc__):])
