"""Systematic counterexample search for the BCAP claim, via the PROVED
reduction  (B cap I_A != {})  <=>  Good(S_G u p*S_A) != {}.
Every hit is re-verified against the LITERAL definition of B.
Run: python3 bcap_search_v1.py
"""
from bcap_attack_v1 import *
from itertools import combinations

PRIMES = [2,3,5,7,11,13,17,19,23]

def search(n, smax, kg_range, ka_range, lrc_shape_only=True, Lcap=6000, pmax=23):
    hits = []
    speeds = list(range(1, smax+1))
    for kg in kg_range:
        for ka in ka_range:
            if lrc_shape_only and kg + ka != n - 1:
                continue
            for SG in combinations(speeds, kg):
                LG = lcm(SG)
                if n*LG > Lcap*n: continue
                if not good_nonempty(n, SG): continue
                for SA in combinations(speeds, ka):
                    if not good_nonempty(n, SA): continue
                    for p in PRIMES:
                        if p > pmax: break
                        if gcd(p, LG) != 1: continue
                        T = sorted(set(SG) | set(p*v for v in SA))
                        if lcm(T) > Lcap: continue
                        if not good_nonempty(n, T):
                            hits.append((n, list(SG), list(SA), p, T))
    return hits

def verify_literal(n, SG, SA, p):
    LG, IG, LA, IA, B = B_direct(n, SG, SA, p)
    return bool(IG), bool(IA), sorted(B & set(IA)), len(B), len(IA), n*LA

if __name__ == "__main__":
    for n, smax, kg_r, ka_r in [(3,6,[1,2],[1,2]), (4,6,[1,2,3],[1,2,3]),
                                (5,7,[1,2,3,4],[1,2,3]), (6,8,[1,2,3,4],[1,2]),
                                (8,8,[5,6],[1,2])]:
        hits = search(n, smax, kg_r, ka_r)
        print(f"=== n={n}, speeds<={smax}, LRC-shape only: {len(hits)} counterexample(s)")
        for h in hits[:12]:
            nn,SG,SA,p,T = h
            ig,ia,inter,lb,lia,nla = verify_literal(nn,SG,SA,p)
            flag = "OK" if (ig and ia and not inter) else "CHECK-FAILED"
            print(f"   S_G={SG} S_A={SA} p={p} -> T={T} | I_G!={{}}:{ig} I_A!={{}}:{ia} "
                  f"B∩I_A={inter} |B|={lb} |I_A|={lia} nL_A={nla} [{flag}]")
        if len(hits)>12: print(f"   ... and {len(hits)-12} more")
