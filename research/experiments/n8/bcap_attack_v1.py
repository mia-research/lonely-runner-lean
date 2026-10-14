"""BCAP: the B-cap-I_A claim of Theorem 5.2-P (lrc_proof_allN_v11_8.md).

Object (verbatim from the task statement):
  Good(S,L) := { m in [0,nL) : for all u in S, floor(m/(L/u)) mod n in [1,n-2] }
  I_G := Good(S_G,L_G), I_A := Good(S_A,L_A)
  N0 := n*L_G*L_A,  W := L_A*p
  B  := union over a in I_G of { floor((m mod N0)/L_G) : m in [a*W, a*W+W) }
Claim: I_G != {} and I_A != {}  ==>  B & I_A != {}.

EXACT ARITHMETIC ONLY: integers throughout; Fraction used only for reporting.
Run:  python3 bcap_attack_v1.py
"""
from fractions import Fraction
from math import gcd
from itertools import combinations
import random, sys

def lcm(xs):
    L = 1
    for x in xs:
        L = L * x // gcd(L, x)
    return L

def good_indices(n, S):
    """Good(S, lcm S) as a sorted list of ints in [0, n*L)."""
    L = lcm(S)
    steps = [L // u for u in S]
    out = []
    for m in range(n * L):
        ok = True
        for s in steps:
            if not (1 <= (m // s) % n <= n - 2):
                ok = False
                break
        if ok:
            out.append(m)
    return L, out

def good_nonempty(n, S):
    """Same predicate, early-exit."""
    L = lcm(S)
    steps = [L // u for u in S]
    for m in range(n * L):
        if all(1 <= (m // s) % n <= n - 2 for s in steps):
            return True
    return False

def B_direct(n, SG, SA, p):
    """B computed literally from the definition (no shortcut)."""
    LG, IG = good_indices(n, SG)
    LA, IA = good_indices(n, SA)
    N0 = n * LG * LA
    W = LA * p
    B = set()
    for a in IG:
        base = a * W
        if W >= N0:                      # band covers a full period
            B = set(range(n * LA))
            break
        for m in range(base, base + W):
            B.add(((m % N0) // LG))
    return LG, IG, LA, IA, B

def B_arcs(n, SG, SA, p):
    """B via the arc simplification: a contributes the cyclic beta-arc
       [ floor(LA*r/LG), floor((LA*r + LA*p - 1)/LG) ], r = a*p mod n*LG."""
    LG, IG = good_indices(n, SG)
    LA, IA = good_indices(n, SA)
    N0 = n * LG * LA
    W = LA * p
    nLA = n * LA
    B = set()
    for a in IG:
        if W >= N0:
            return LG, IG, LA, IA, set(range(nLA))
        r = (a * p) % (n * LG)
        s = LA * r
        lo = s // LG
        hi = (s + W - 1) // LG
        for b in range(lo, hi + 1):
            B.add(b % nLA)
    return LG, IG, LA, IA, B

def claim_holds(n, SG, SA, p, use_arcs=False):
    f = B_arcs if use_arcs else B_direct
    LG, IG, LA, IA, B = f(n, SG, SA, p)
    if not IG or not IA:
        return None                      # hypothesis vacuous
    return bool(B & set(IA))

def reformulation(n, SG, SA, p):
    """PROVED-equivalent form: Good(S_G  u  p*S_A) nonempty."""
    T = sorted(set(SG) | set(p * v for v in SA))
    return good_nonempty(n, T)
