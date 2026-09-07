#!/usr/bin/env python3
"""Theorem 5.2-P' -- replace the pigeonhole COUNT by the direct INTERSECTION test.

--- VERBATIM SOURCE, lrc_proof_allN_v11_8.md L648-656 (proof of Theorem 5.2-P) ---
  "By the pigeonhole principle applied to B, I_A subset {0,...,n L_A - 1}: if
   |B| + |I_A| > n L_A, then B n I_A != empty.  Choose any beta_0 in B n I_A.  By
   definition of B, there exist alpha_0 in I_G and m'' in [alpha_0 L_A p,
   (alpha_0+1) L_A p) ... such that ... alpha(m'') = alpha_0 in I_G and
   beta(m'') = beta_0 in I_A, hence is a joint-good fine cell ... The midpoint of
   F_{m''} is the required witness."

So the cardinality inequality is used ONLY to force B n I_A non-empty.  The hypothesis
actually needed is B n I_A != empty.  Call that Theorem 5.2-P'; it is strictly weaker as
a hypothesis, hence strictly stronger as a criterion, and the witness construction is
unchanged.  Remark 5.2-P (L668-674) already records that the count is lossy: "3,158
positive inputs (8.3%) still satisfy the conjecture's conclusion even when pigeonhole
fails -- these witnesses arise from arithmetic alignment between B and I_A that exceeds
what the union bound guarantees."

EXACTNESS: integers and Fraction only.  No float anywhere, including in reporting --
ratios are printed as exact Fraction.  (Prior runs had float percentage prints; the
decision paths were exact, but this file has no float at all.)
"""
import sys
from fractions import Fraction as F
from math import gcd, lcm
from itertools import combinations
sys.path.insert(0, "experiments/n8")
from escape_coverage_v1 import norm, largest_prime, escape_ii, witness_ii
from escape_coverage_v2 import good_idx, band_B, witness11

n = 8; CAP = 10**6

def config(T):
    """Return (arm, G-speeds, L_G, A-speeds, L_A, p) or None."""
    V = T[-1]; slow = list(T[:-1]); p = largest_prime(V); q = V // p
    if not ((n - 1) * slow[0] < V <= (n - 1) * slow[-1]): return None
    if gcd(p, lcm(*slow)) == 1:
        return ("10.1", slow, lcm(*slow), [q], q, p)
    S = [v for v in slow if v % p]; ws = [v // p for v in slow if v % p == 0]
    if not S or not ws: return None
    L_G = lcm(*S) if len(S) > 1 else S[0]
    Asp = sorted(set(ws + [q])); L_A = lcm(*Asp) if len(Asp) > 1 else Asp[0]
    return ("11.1", S, L_G, Asp, L_A, p)

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    stat = {}
    for T in combinations(range(1, B + 1), 7):
        if gcd(*T) != 1: continue
        c = config(T)
        if c is None: continue
        arm, Gsp, L_G, Asp, L_A, p = c
        if L_G > CAP or n * L_A > 4 * CAP: continue
        d = stat.setdefault(arm, {"tot":0,"pig":0,"inter":0,"ii":0,"old":0,"new":0,
                                  "resid":[],"wfail":0})
        d["tot"] += 1
        Bn, seen = band_B(Gsp, L_G, Asp, L_A, p)
        IA = [b for b in range(n * L_A) if good_idx(b, Asp, L_A)]
        pig = (Bn + len(IA) > n * L_A)                 # Theorem 5.2-P  (count)
        inter = any(seen[b] for b in IA)               # Theorem 5.2-P' (intersection)
        e2 = escape_ii(T)
        d["pig"] += pig; d["inter"] += inter; d["ii"] += e2
        d["old"] += (e2 or pig); d["new"] += (e2 or inter)
        if not (e2 or inter): d["resid"].append(T)
        # CONTROL: whenever the NEW criterion fires, build and verify its witness exactly
        if inter and not pig:
            aux = (Gsp, L_G, Asp, L_A, p, seen, set(IA))
            t = witness11(T, aux) if arm == "11.1" else witness11(T, aux)
            if t is None or not all(norm(t * v) >= F(1, n) for v in T): d["wfail"] += 1
    print(f"n=8, speeds <= {B}, gcd=1, hard case.  Exact arithmetic; ratios are Fractions.")
    for arm in ("10.1", "11.1"):
        if arm not in stat: continue
        d = stat[arm]; t = d["tot"]
        print(f"\n  THEOREM {arm}   arm size {t}")
        print(f"    escape (ii) Lemma 5.2-D          : {d['ii']}")
        print(f"    (iii) 5.2-P   pigeonhole COUNT   : {d['pig']}")
        print(f"    (iii') 5.2-P' direct INTERSECTION: {d['inter']}")
        print(f"    coverage OLD (ii or count)       : {d['old']}/{t} = {F(d['old'],t)}")
        print(f"    coverage NEW (ii or intersection): {d['new']}/{t} = {F(d['new'],t)}")
        print(f"    RESIDUAL: {t-d['new']}   (was {t-d['old']})")
        print(f"    witness failures on newly-covered (must be 0): {d['wfail']}")
        if d["resid"] and len(d["resid"]) <= 40:
            for X in d["resid"]: print("      ", list(X))
