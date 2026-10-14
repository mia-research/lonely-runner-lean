"""n=8 LRC-shape counterexamples with NO speed coincidences:
   S_G, S_A disjoint AND p*S_A disjoint from S_G (so S_G u p*S_A has 7 distinct speeds).
Tightness decided by exact max-min gap when the cell scan is too large.
Run: python3 bcap_disjoint_v1.py
"""
from fractions import Fraction as F
from itertools import combinations
from bcap_attack_v1 import *
from bcap_tightness_v1 import maxmin_gap

CAP = 400000
def good_ne(n, S):
    L = lcm(S); steps = [L//u for u in S]
    lim = n*L
    for m in range(min(lim, CAP)):
        if all(1 <= (m//s) % n <= n-2 for s in steps): return True
    if lim <= CAP: return False
    g,_ = maxmin_gap(S)                      # exact fallback
    return g > F(1, n)

_c = {}
def gne(n,S):
    k=(n,tuple(sorted(set(S))))
    if k not in _c: _c[k]=good_ne(n,S)
    return _c[k]

if __name__=="__main__":
    n=8; PR=[2,3,5,7,11,13]; SM=14   # ~4 min
    hits=[]
    for kg,ka in ((6,1),(5,2),(4,3)):
        for SG in combinations(range(1,SM+1),kg):
            LG=lcm(SG)
            if LG>5000 or not gne(n,SG): continue
            sg=set(SG)
            for SA in combinations(range(1,SM+1),ka):
                if sg & set(SA): continue                 # disjoint speed sets
                if not gne(n,SA): continue
                for p in PR:
                    if gcd(p,LG)!=1: continue
                    pSA=set(p*v for v in SA)
                    if sg & pSA: continue                 # no coincidence after scaling
                    T=tuple(sorted(sg|pSA))
                    if len(T)!=7: continue
                    if max(T)>60: continue
                    if not gne(n,T):
                        hits.append((list(SG),list(SA),p,list(T)))
    print(f"n=8, LRC-shape, speeds<=%d, fully disjoint: %d counterexamples"%(SM,len(hits)))
    seen=set()
    for SG,SA,p,T in hits:
        LG,IG,LA,IA,B = B_direct(n,SG,SA,p)
        inter=sorted(B&set(IA))
        g,_=maxmin_gap(T)
        tag = "" if tuple(T) in seen else "  <-- new tight set"
        seen.add(tuple(T))
        print(f"  S_G={SG} S_A={SA} p={p} -> T={T} gap={g} | |I_G|={len(IG)} |I_A|={len(IA)} "
              f"|B|={len(B)} nL_A={n*LA} B∩I_A={inter}{tag}")
