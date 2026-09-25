"""Is the mirror of the top pair special, or does any modulus of its size work?

pair_moduli_v1/v2 and hard_search_v1: on every hard set found (no q <= 8 certifies), some
t = k/(a+b) is lonely, a < b the two largest.  But a modulus near 2*d_max offers ~2*d_max instants,
and six effective constraints each blocking ~1/4 of them would still leave some by chance.
Control: the same test k/Q, 0 < k < Q, with Q replaced by moduli of comparable size and no
mirror structure.  Reported, on the 1,436 hard sets with largest 41..60 (hard_search_v1, exhaustive)
and on 3,000 random non-hard residual sets of [1,60]: the fraction of sets with a lonely k/Q, and
the mean fraction of k in 1..Q-1 that are lonely.
"""
import itertools, json, random, time
from collections import defaultdict
import os
HERE = os.path.dirname(os.path.abspath(__file__))
_rs = __file__.replace('mirror_control_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def good_ks(S, Q): return [k for k in range(1, Q) if all(Q <= 8 * (d * k % Q) <= 7 * Q for d in S)]

def moduli(S):
    c, a, b = sorted(S)[-3:]
    return {'mirror a+b': a + b, 'a+b-1': a + b - 1, 'a+b+1': a + b + 1, 'a+b-2': a + b - 2,
            'a+b+2': a + b + 2, 'b+c': b + c, 'a+c': a + c, 'b': b, 'a': a, '2b': 2 * b, 'b-a': b - a}

def report(sets, label):
    hit = defaultdict(int); dens = defaultdict(float)
    for S in sets:
        for name, Q in moduli(S).items():
            if Q < 2: continue
            g = good_ks(S, Q); hit[name] += bool(g); dens[name] += len(g) / (Q - 1)
    print(f"{label} ({len(sets)} sets): modulus -> sets with a lonely k/Q, mean fraction of k lonely")
    for name in moduli(sets[0]):
        print(f"   {name:10s} {hit[name]:5d} ({100*hit[name]/len(sets):5.1f}%)   {100*dens[name]/len(sets):5.2f}%")

t0 = time.time()
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
report(H, "hard sets, largest 41..60")
random.seed(11); easy = []
while len(easy) < 3000:
    S = tuple(sorted(random.sample(range(1, 61), 7)))
    if eight_residual(S) and any(rule(S, q, free_exact) for q in range(2, 9)): easy.append(S)
report(easy, "non-hard residual sets of [1,60]")
print(f"total {time.time()-t0:.0f}s")
