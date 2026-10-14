"""n=8 LRC-shape counterexamples with DISTINCT RUNNER SPEEDS:
   the actual runner set is S_G u p*S_A, so the condition that matters is
   p*S_A n S_G = empty and |S_G| + |S_A| = n-1 (so |T| = n-1 = 7 distinct speeds).
   (S_A n S_G may be nonempty: raw A-speeds are not runner speeds.)
Run: python3 bcap_runnerdistinct_v1.py
"""
from fractions import Fraction as F
from itertools import combinations
from bcap_attack_v1 import *
from bcap_tightness_v1 import maxmin_gap
from bcap_disjoint_v1 import gne

if __name__=="__main__":
    n=8; PR=[2,3,5,7,11,13]; SM=12
    hits=[]
    for kg,ka in ((6,1),(5,2),(4,3)):
        for SG in combinations(range(1,SM+1),kg):
            LG=lcm(SG)
            if LG>5000 or not gne(n,SG): continue
            sg=set(SG)
            for SA in combinations(range(1,SM+1),ka):
                if not gne(n,SA): continue
                for p in PR:
                    if gcd(p,LG)!=1: continue
                    pSA=set(p*v for v in SA)
                    if sg & pSA: continue            # runner speeds distinct
                    if len(pSA)!=ka: continue
                    T=tuple(sorted(sg|pSA))
                    if len(T)!=n-1 or max(T)>60: continue
                    if not gne(n,T): hits.append((list(SG),list(SA),p,list(T)))
    print(f"n=8, LRC-shape, speeds<={SM}, runner speeds distinct: {len(hits)} counterexamples")
    for SG,SA,p,T in hits:
        LG,IG,LA,IA,B=B_direct(n,SG,SA,p)
        g,_=maxmin_gap(T)
        print(f"  S_G={SG} S_A={SA} p={p} -> runners T={T} gap={g}")
        print(f"     L_G={LG} L_A={LA} |I_G|={len(IG)} |I_A|={len(IA)} |B|={len(B)} "
              f"nL_A={n*LA} |B|+|I_A|={len(B)+len(IA)}  B∩I_A={sorted(B&set(IA))}")
