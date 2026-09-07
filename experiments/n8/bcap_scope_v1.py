"""(1) Lemma check: Good(T)=empty  <=>  maxmin gap(T) <= 1/n.
   (2) Wider n=8 LRC-shape counterexample scan; collects the tight sets T.
   (3) Theorem C firing rate (max cyclic run c in I_G with p*c >= n*L_G).
Run: python3 bcap_scope_v1.py
"""
from fractions import Fraction as F
from itertools import combinations
from bcap_attack_v1 import *
from bcap_tightness_v1 import maxmin_gap

_gn = {}
def gn(n, S):
    k = (n, tuple(sorted(set(S))))
    if k not in _gn: _gn[k] = good_nonempty(n, S)
    return _gn[k]

def max_run(IG, mod):
    s = set(IG)
    if len(s) == mod: return mod
    best = 0
    for a in s:
        if (a-1) % mod in s: continue
        c = 0; x = a
        while x in s: c += 1; x = (x+1) % mod
        best = max(best, c)
    return best

if __name__ == "__main__":
    # (1) lemma check over all 3- and 4-subsets of [1..9] at n=4,5,6
    bad = 0; tot = 0
    for n in (4,5,6):
        for k in (2,3,4):
            for T in combinations(range(1,10), k):
                if lcm(T) > 2000: continue
                g,_ = maxmin_gap(T)
                e1 = not gn(n, T)          # Good empty
                e2 = (g <= F(1,n))         # gap <= 1/n
                tot += 1
                if e1 != e2:
                    bad += 1
                    if bad <= 3: print("  LEMMA MISMATCH", n, T, g, e1, e2)
    print(f"(1) Good(T)=empty <=> gap<=1/n : {tot} sets tested, {bad} mismatches")

    # (2) n=8 LRC-shape scan, speeds <= 10, p <= 13
    n = 8; PR = [2,3,5,7,11,13]
    hits = []; tights = {}
    for kg, ka in ((6,1),(5,2),(4,3)):
        for SG in combinations(range(1,11), kg):
            LG = lcm(SG)
            if LG > 3000 or not gn(n, SG): continue
            for SA in combinations(range(1,11), ka):
                if not gn(n, SA): continue
                for p in PR:
                    if gcd(p, LG) != 1: continue
                    T = tuple(sorted(set(SG) | set(p*v for v in SA)))
                    if lcm(T) > 6000: continue
                    if not gn(n, T):
                        hits.append((list(SG), list(SA), p, list(T)))
                        tights[T] = tights.get(T, 0) + 1
    print(f"(2) n=8 LRC-shape, speeds<=10, p<=13: {len(hits)} counterexamples, "
          f"{len(tights)} distinct tight sets T")
    for T, c in sorted(tights.items(), key=lambda kv: -kv[1]):
        g,_ = maxmin_gap(T)
        print(f"     T={list(T)}  gap={g}  |T|={len(T)}  decompositions={c}")

    # (3) Theorem C firing on the recorded counterexamples + on random positives
    print("(3) Theorem C (p * maxrun(I_G) >= n*L_G) on the n=8 counterexamples:")
    for SG, SA, p, T in hits[:6]:
        LG, IG = good_indices(n, SG)
        c = max_run(IG, n*LG)
        print(f"     S_G={SG} p={p}: |I_G|={len(IG)} maxrun={c} p*c={p*c} nL_G={n*LG} "
              f"fires={p*c >= n*LG}")
