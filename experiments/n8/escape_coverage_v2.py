#!/usr/bin/env python3
"""Escape coverage, BOTH arms.  Adds Theorem 11.1 to escape_coverage_v1.py's 10.1 arm.

PRE-REGISTRATION: this is an extension of docs/n8/PREREG_ESCAPE_COVERAGE_v1.md with
sections 2 (statistic), 5 (constructive-witness control), 6 (exactness), 8-9 (scope and
pre-commitments) applying VERBATIM.  The only change is the configuration fed to
Theorem 5.2.  Deviation recorded: v1's spec declared Theorem 11.1 out of scope; this arm
is that out-of-scope set, measured with the identical design.

--- VERBATIM SOURCE, lrc_proof_allN_v11_8.md L1458-1478 (Theorem 11.1) ---
  "suppose the largest prime p of V satisfies p | v_{j_k} for k = 1,...,r (with r >= 1)
   ... Write w_k = v_{j_k}/p ... and q = V/p.  Then G_s n G_V != empty, unconditionally if
   any of the following hold: (i) p >= n lcm(S_ind); (ii) ... Lemma 5.2-D ...;
   (iii) the band beta-coverage B and target index set I_A for the sec 11.1 configuration
   (G_ind, jointGoodSet(w_1,...,w_r,q), p) satisfy |B| + |I_A| > n L_A;
   (iv) the bands are pairwise disjoint and p/v_max + 1/u_max > n(n-1)/2, with
   v_max = max over S_ind and u_max = max(w_1,...,w_r,q)."
--- VERBATIM SOURCE, L1490-1496 (Step 1) ---
  "S_ind = {v_j : p does not divide v_j} ... G_ind = {t : ||v_j t|| >= 1/n for all
   v_j in S_ind}."
--- VERBATIM SOURCE, L1502-1508 (Step 2) ---
  "A = {phi : ||w_k phi|| >= 1/n for all k, ||q phi|| >= 1/n}.  A is the good set for the
   r+1 distinct positive integer speeds (w_1,...,w_r,q)."
--- VERBATIM SOURCE, L1530 (Step 3):  L_ind = lcm(S_ind), gcd(p, L_ind) = 1. ---
"""
import sys
from fractions import Fraction as F
from math import gcd, lcm
from itertools import combinations
sys.path.insert(0, "experiments/n8")
from escape_coverage_v1 import norm, largest_prime, escape_ii, witness_ii

n = 8
CAP = 10**6

def good_idx(m, speeds, L, nn=n):
    """Step-1/Step-2 dichotomy: index m is good iff floor(m/(L/u)) mod n in [1, n-2]."""
    for u in speeds:
        if not (1 <= (m // (L // u)) % nn <= nn - 2): return False
    return True

def band_B(Gsp, L_G, Asp, L_A, p):
    """B := union over alpha_0 in I_G of { floor((m'' mod n L_G L_A)/L_G) :
       m'' in [alpha_0 L_A p, (alpha_0+1) L_A p) }   (Theorem 5.2-P, L632-646)."""
    NLG, NLA, N0, W = n * L_G, n * L_A, n * L_G * L_A, L_A * p
    seen = bytearray(NLA); cnt = 0
    for m in range(NLG):
        if not good_idx(m, Gsp, L_G): continue
        start = (m * W) % N0
        b0, b1 = start // L_G, (start + W - 1) // L_G
        span = b1 - b0
        rng = range(NLA) if span >= NLA - 1 else ((b0 + k) % NLA for k in range(span + 1))
        for b in rng:
            if not seen[b]:
                seen[b] = 1; cnt += 1
                if cnt == NLA: return cnt, seen
    return cnt, seen

def arm11(T):
    V = T[-1]; slow = list(T[:-1]); p = largest_prime(V); q = V // p
    S_ind = [v for v in slow if v % p]
    ws = [v // p for v in slow if v % p == 0]
    if not S_ind or not ws: return None
    L_G = lcm(*S_ind) if len(S_ind) > 1 else S_ind[0]
    Asp = sorted(set(ws + [q]))
    L_A = lcm(*Asp) if len(Asp) > 1 else Asp[0]
    if L_G > CAP or n * L_A > 4 * CAP: return ("capped",)
    e1 = p >= n * L_G                                    # escape (i) -- NOT proved vacuous here
    e4 = F(p, max(S_ind)) + F(1, max(Asp)) > F(n * (n - 1), 2)   # (iv) inequality half
    e2 = escape_ii(T)
    Bn, seen = band_B(S_ind, L_G, Asp, L_A, p)
    IA = [b for b in range(n * L_A) if good_idx(b, Asp, L_A)]
    e3 = (Bn + len(IA) > n * L_A)
    return ("ok", e1, e2, e3, e4, (S_ind, L_G, Asp, L_A, p, seen, set(IA)))

def witness11(T, aux):
    S_ind, L_G, Asp, L_A, p, seen, IAset = aux
    M = n * L_G * L_A * p; W = L_A * p; N0 = n * L_G * L_A
    for m in range(n * L_G):
        if not good_idx(m, S_ind, L_G): continue
        for mpp in range(m * W, (m + 1) * W):
            if (mpp % N0) // L_G in IAset:
                return F(2 * mpp + 1, 2 * M)
    return None

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    cells = {"ii_only":0,"iii_only":0,"both":0,"neither":0}
    tot = capped = f1 = f4 = 0; residual = []; wfail = []
    for T in combinations(range(1, B + 1), 7):
        if gcd(*T) != 1: continue
        V = T[-1]; slow = list(T[:-1])
        if not ((n-1)*slow[0] < V <= (n-1)*slow[-1]): continue
        if gcd(largest_prime(V), lcm(*slow)) == 1: continue      # -> Theorem 10.1
        r = arm11(T)
        if r is None: continue
        if r[0] == "capped": capped += 1; continue
        _, e1, e2, e3, e4, aux = r
        tot += 1; f1 += e1; f4 += e4
        if e2 and e3: cells["both"] += 1
        elif e2: cells["ii_only"] += 1
        elif e3: cells["iii_only"] += 1
        else: cells["neither"] += 1; residual.append(T)
        if e2:
            t = witness_ii(T)
            if not all(norm(t*v) >= F(1,n) for v in T): wfail.append(("ii",T))
        if e3:
            t = witness11(T, aux)
            if t is None or not all(norm(t*v) >= F(1,n) for v in T): wfail.append(("iii",T))
    print(f"THEOREM 11.1 ARM  n=8, speeds <= {B}, gcd=1, hard case, gcd(p,L_G) > 1")
    print(f"  arm size                                  : {tot}")
    print(f"  compute-cap exclusions                    : {capped}")
    print(f"  escape (i)  p >= n*lcm(S_ind)   fires     : {f1}")
    print(f"  escape (iv) inequality half     fires     : {f4}")
    if tot:
        print(f"  MARGINALS   (ii) Lemma 5.2-D : {cells['ii_only']+cells['both']:>6}"
              f"  ({100.0*(cells['ii_only']+cells['both'])/tot:.2f}%)")
        print(f"              (iii) Thm 5.2-P  : {cells['iii_only']+cells['both']:>6}"
              f"  ({100.0*(cells['iii_only']+cells['both'])/tot:.2f}%)")
        print(f"  4-CELL  ii only {cells['ii_only']}  iii only {cells['iii_only']}"
              f"  both {cells['both']}  NEITHER {cells['neither']}")
        print(f"  COVERAGE (ii or iii) : {tot-cells['neither']}/{tot}"
              f" = {100.0*(tot-cells['neither'])/tot:.2f}%")
    print(f"  witness-verification failures (must be 0) : {len(wfail)}")
    if wfail: print("   ", wfail[:5])
    if residual and len(residual) <= 200:
        print(f"  RESIDUAL ({len(residual)}):")
        for T in residual[:60]: print("   ", list(T))
