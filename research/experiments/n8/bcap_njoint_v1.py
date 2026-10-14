"""Independent recomputation of N_joint (Remark 5.2-P's own statistic):
   N_joint := #{ m'' in [0, M) : alpha(m'') in I_G  and  beta(m'') in I_A },
   M = n*L_G*L_A*p,  alpha = floor(m''/(L_A p)),  beta = floor((m'' mod n L_G L_A)/L_G).
This is computed from scratch, NOT via B, as a cross-check.
Then: exhaustive LRC-shape counterexample scan inside the stated range of
Remark 5.2-P  (n<=7, |S_G|<=3, |S_A|<=2, p<=19, hard regime p < n L_G).
Run: python3 bcap_njoint_v1.py
"""
from itertools import combinations
from bcap_attack_v1 import *

def n_joint(n, SG, SA, p):
    LG, IG = good_indices(n, SG)
    LA, IA = good_indices(n, SA)
    sIG, sIA = set(IG), set(IA)
    M = n * LG * LA * p
    N0 = n * LG * LA
    cnt = 0
    for m2 in range(M):
        if (m2 // (LA * p)) in sIG and ((m2 % N0) // LG) in sIA:
            cnt += 1
    return LG, LA, len(IG), len(IA), M, cnt

if __name__ == "__main__":
    print("--- headline verifications (N_joint from scratch) ---")
    for n, SG, SA, p in [(5,[1,3],[1,2],2), (8,[1,2,3,4,5,6],[1],7), (3,[1],[1],2)]:
        LG, LA, ig, ia, M, c = n_joint(n, SG, SA, p)
        print(f"n={n} S_G={SG} S_A={SA} p={p}: L_G={LG} L_A={LA} |I_G|={ig} |I_A|={ia} "
              f"M={M} hard-regime(p<nL_G)={p < n*LG} N_joint={c}")

    print("\n--- exhaustive scan inside Remark 5.2-P's stated range ---")
    print("    n<=7, |S_G|<=3, |S_A|<=2, p<=19 prime, gcd(p,L_G)=1,")
    print("    LRC-shape (k_G+k_A = n-1), hard regime (p < n L_G), speeds <= 12")
    PR = [2,3,5,7,11,13,17,19]
    found = []; scanned = 0
    for n in range(3, 8):
        for kg in range(1, 4):
            ka = n - 1 - kg
            if not (1 <= ka <= 2): continue
            for SG in combinations(range(1,13), kg):
                LG = lcm(SG)
                if LG > 900: continue
                _, IG = good_indices(n, SG)
                if not IG: continue
                for SA in combinations(range(1,13), ka):
                    _, IA = good_indices(n, SA)
                    if not IA: continue
                    for p in PR:
                        if gcd(p, LG) != 1: continue
                        if p >= n * LG: continue          # hard regime only
                        scanned += 1
                        T = sorted(set(SG) | set(p*v for v in SA))
                        if lcm(T) > 3000: continue
                        if not good_nonempty(n, T):
                            found.append((n, list(SG), list(SA), p, T))
    print(f"    inputs scanned: {scanned};  counterexamples (N_joint = 0): {len(found)}")
    for n, SG, SA, p, T in found:
        LG, LA, ig, ia, M, c = n_joint(n, SG, SA, p)
        print(f"      n={n} S_G={SG} S_A={SA} p={p} -> T={T} | N_joint={c} "
              f"|I_G|={ig} |I_A|={ia} delta={len(SG)+len(SA)-(n-1)}")
