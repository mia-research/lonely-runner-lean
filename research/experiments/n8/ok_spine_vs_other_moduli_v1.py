"""When a runner loses the mod-8 spine, where does its isolation actually live?

Tests HANDOVER_2026_09_12 §2 item 7 ("a mod-8 sharer can be lonely on another m-grid") and
§4 (a runner keeps all four p/8 instants unless one of ITS OWN differences is = 0 mod 8).

n = |V| = 8 throughout: eight integer speeds, threshold 1/8, seven differences per runner.
Translation only, never adjoining.
"""
import sys, os, random
from fractions import Fraction as F
from math import gcd
from functools import reduce
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def reduce_cfg(V):
    V = sorted(V); g = reduce(gcd, [v-V[0] for v in V[1:]])
    return tuple((v-V[0])//g for v in V)

def lonely_at(D, t):
    for d in D:
        r = (d*t) % 1
        if min(r, 1-r) < F(1, 8): return False
    return True

def smallest_witness(D, qmax=240):
    """smallest-denominator t in (0,1) with all ||d t|| >= 1/8"""
    for q in range(1, qmax+1):
        for p in range(1, q):
            if gcd(p, q) != 1: continue
            if lonely_at(D, F(p, q)): return F(p, q)
    return None

def main(trials=700, hi=40, seed=9):
    rng = random.Random(seed)
    spine = 0; nonspine = 0; nonspine_lonely = 0; dens = {}
    for _ in range(trials):
        V = sorted(rng.sample(range(0, hi), 8))
        assert len(V) == 8, "n = |V| must be 8"
        U = reduce_cfg(V)
        if len(set(U)) < 8: continue
        for u in U:
            D = sorted({abs(w-u) for w in U if w != u})
            # §4: the spine is held iff none of THIS runner's own differences is = 0 mod 8
            holds = all(d % 8 != 0 for d in D)
            # control: that predicate must agree with evaluating t = p/8 directly
            direct = any(lonely_at(D, F(p, 8)) for p in (1, 3, 5, 7))
            assert holds == direct, f"spine predicate disagrees with direct evaluation: {D}"
            if holds: spine += 1; continue
            nonspine += 1
            w = smallest_witness(D)
            if w is not None:
                nonspine_lonely += 1
                dens[w.denominator] = dens.get(w.denominator, 0) + 1
    print(f"n = |V| = 8, integer speeds in [0,{hi}), seed {seed}")
    print("control: spine predicate (no own difference = 0 mod 8) vs direct evaluation at")
    print("         t = p/8 -- asserted equal on every runner, no failures\n")
    print(f"  lonely at a mod-8 grid time (spine holders) : {spine}")
    print(f"  NOT lonely at any mod-8 grid time           : {nonspine}")
    print(f"     of those, lonely at some OTHER time      : {nonspine_lonely} "
          f"({100*nonspine_lonely/max(nonspine,1):.1f}%)\n")
    print("  smallest witness denominator for the spine-losers:")
    for q in sorted(dens): print(f"     q={q:<4} {dens[q]}")
    d8 = sum(v for q, v in dens.items() if q % 8 == 0)
    print(f"\n  denominator divisible by 8: {d8}   not divisible by 8: {sum(dens.values())-d8}")

if __name__ == "__main__":
    main()
