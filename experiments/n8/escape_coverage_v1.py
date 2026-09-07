#!/usr/bin/env python3
"""Coverage of the two unconditional escapes that CAN fire at n=8.
Executes docs/n8/PREREG_ESCAPE_COVERAGE_v1.md.  Integer/Fraction only; no float.

Escapes (i) and (iv) are vacuous in the hard case: PROVED for Thm 10.1
(lcm(slow) >= v_{n-2} so n*lcm > (n-1)v_{n-2} >= V >= p; and p/v_max <= n-1, 1/q <= 1,
so LHS(iv) <= n < n(n-1)/2 for n >= 4); EMPIRICAL only for Thm 11.1 (0 of 97503 at B=24).

--- VERBATIM SOURCE, lrc_proof_allN_v11_8.md L1006-1013 (Lemma 5.2-D) ---
  "Let n >= 3 and let v_1 < v_2 < ... < v_{n-1} be distinct positive integers (here
   v_{n-1} may denote the fast runner V).  Suppose that for every j = 1, ..., n-1 the
   residue v_j mod (n v_1) lies in [v_1, (n-1) v_1].  Then t* := 1/(n v_1) is an LRC
   certificate: ||v_j t*|| >= 1/n for every j."
--- VERBATIM SOURCE, L816-857 (Step 1, cell dichotomy for G; I_G) ---
  "set s_i := L_G/v_i ... a_{i,m} := floor(m / s_i) mod n ... the open interior of
   C_m^(G) is contained in G iff a_{i,m} in [1, n-2] for every i ... Call m a G-good
   index ... m in I_G."   Cells C_m^(G) = [m/(n L_G), (m+1)/(n L_G)), m in [0, n L_G).
--- VERBATIM SOURCE, L859-863 (Step 2; I_A) ---
  "partition [0,1) into n L_A cells ... The A-good indices I_A are defined by the same
   condition with u_j, L_A in place of v_i, L_G."
--- VERBATIM SOURCE, L872-874 (Step 3; alpha, beta) ---
  "alpha(m'') := floor(m''/(L_A . p)) in [0, n L_G),
   beta(m'')  := floor((m'' mod (n L_G L_A))/L_G) in [0, n L_A)."
--- VERBATIM SOURCE, L632-646 (Theorem 5.2-P) ---
  "B := union over alpha_0 in I_G of { floor((m'' mod n L_G L_A)/L_G) :
   m'' in [alpha_0 . L_A p, (alpha_0 + 1) . L_A p) }  subset of {0,...,n L_A - 1}.
   If |B| + |I_A| > n L_A, then G n {t : {pt} in A} != empty."
"""
import sys
from fractions import Fraction as F
from math import gcd, lcm
from itertools import combinations

n = 8

def norm(x):
    assert isinstance(x, F), "float on signal path"
    r = x - (x.numerator // x.denominator)
    return min(r, 1 - r)

def largest_prime(x):
    f, d, best = x, 2, 1
    while d * d <= f:
        while f % d == 0: best = d; f //= d
        d += 1
    return max(best, f) if f > 1 else best

# ---- escape (ii): Lemma 5.2-D -------------------------------------------------
def escape_ii(T):
    v1 = min(T); mod = n * v1
    return all(v1 <= (v % mod) <= (n - 1) * v1 for v in T)

def witness_ii(T):
    return F(1, n * min(T))

# ---- escape (iii): Theorem 5.2-P ----------------------------------------------
def IG_and_B(slow, L_G, L_A, p):
    """I_G by the Step-1 dichotomy; B by the Theorem 5.2-P union.  Returns (|B|, sample)."""
    s = [L_G // v for v in slow]
    NLG, NLA, N0, W = n * L_G, n * L_A, n * L_G * L_A, L_A * p
    seen = bytearray(NLA); cnt = 0; sample = None
    for m in range(NLG):
        ok = True
        for si in s:
            if not (1 <= (m // si) % n <= n - 2): ok = False; break
        if not ok: continue
        start = (m * W) % N0
        b0 = start // L_G
        b1 = (start + W - 1) // L_G
        span = b1 - b0
        if span >= NLA - 1:
            rng = range(NLA)
        else:
            rng = ((b0 + k) % NLA for k in range(span + 1))
        for b in rng:
            if not seen[b]:
                seen[b] = 1; cnt += 1
                if sample is None: sample = (m, b)
        if cnt == NLA: break
    return cnt, seen, sample

def escape_iii(slow, V, p, q):
    L_G = lcm(*slow); L_A = q
    if L_G > 10**6: return None, None, None          # declared compute cap (prereg sec 3)
    Bn, seen, sample = IG_and_B(slow, L_G, L_A, p)
    IA = [b for b in range(n * L_A) if 1 <= b % n <= n - 2]
    return (Bn + len(IA) > n * L_A), (L_G, L_A, seen, IA), sample

def witness_iii(slow, V, p, q, aux, sample):
    """Fine-cell midpoint (2m''+1)/(2M), M = n L_G L_A p, for some m'' with
    alpha(m'') in I_G and beta(m'') in I_A."""
    L_G, L_A, seen, IA = aux
    IAset = set(IA); M = n * L_G * L_A * p; W = L_A * p; N0 = n * L_G * L_A
    s = [L_G // v for v in slow]
    for m in range(n * L_G):
        if not all(1 <= (m // si) % n <= n - 2 for si in s): continue
        for mpp in range(m * W, (m + 1) * W):
            if (mpp % N0) // L_G in IAset:
                return F(2 * mpp + 1, 2 * M)
    return None

# ---- classification ------------------------------------------------------------
def classify(T):
    V = T[-1]; slow = list(T[:-1])
    if not ((n - 1) * slow[0] < V <= (n - 1) * slow[-1]): return None
    L = lcm(*slow); p = largest_prime(V); q = V // p
    arm = "10.1" if gcd(p, L) == 1 else "11.1"
    if arm == "11.1": return ("11.1", None, None, None, None)
    e2 = escape_ii(T)
    e3, aux, sample = escape_iii(slow, V, p, q)
    return (arm, e2, e3, aux, (slow, V, p, q, sample))

if __name__ == "__main__":
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    pilot = "--pilot" in sys.argv
    cells = {"ii_only": 0, "iii_only": 0, "both": 0, "neither": 0}
    n10 = n11 = capped = 0; residual = []; wfail = []
    for T in combinations(range(1, B + 1), 7):
        if gcd(*T) != 1: continue
        r = classify(T)
        if r is None: continue
        arm, e2, e3, aux, meta = r
        if arm == "11.1": n11 += 1; continue
        if e3 is None: capped += 1; continue
        n10 += 1
        if e2 and e3: cells["both"] += 1
        elif e2: cells["ii_only"] += 1
        elif e3: cells["iii_only"] += 1
        else: cells["neither"] += 1; residual.append(T)
        # CONTROL: a firing escape must produce a verified witness
        if e2:
            t = witness_ii(T)
            if not all(norm(t * v) >= F(1, n) for v in T): wfail.append(("ii", T))
        if e3:
            slow, V, p, q, sample = meta
            t = witness_iii(slow, V, p, q, aux, sample)
            if t is None or not all(norm(t * v) >= F(1, n) for v in T): wfail.append(("iii", T))
    tot = n10
    print(f"{'PILOT' if pilot else 'RUN'}  n=8, speeds <= {B}, gcd=1, hard case")
    print(f"  Theorem 11.1 (out of scope, gcd(p,L_G)>1) : {n11}")
    print(f"  compute-cap exclusions (L_G > 1e6)        : {capped}")
    print(f"  Theorem 10.1 arm                          : {tot}")
    if tot:
        print(f"  MARGINALS   escape (ii) Lemma 5.2-D : {cells['ii_only']+cells['both']:>6}"
              f"  ({100.0*(cells['ii_only']+cells['both'])/tot:.2f}%)")
        print(f"              escape (iii) Thm 5.2-P  : {cells['iii_only']+cells['both']:>6}"
              f"  ({100.0*(cells['iii_only']+cells['both'])/tot:.2f}%)")
        print(f"  4-CELL  ii only {cells['ii_only']}  iii only {cells['iii_only']}"
              f"  both {cells['both']}  NEITHER {cells['neither']}")
        print(f"  COVERAGE (ii or iii) : {tot-cells['neither']}/{tot}"
              f"  = {100.0*(tot-cells['neither'])/tot:.2f}%")
    print(f"  witness-verification failures (must be 0) : {len(wfail)}")
    if wfail: print("   ", wfail[:5])
    if residual and len(residual) <= 200:
        print(f"  RESIDUAL tuples ({len(residual)}):")
        for T in residual[:60]: print("   ", list(T))
