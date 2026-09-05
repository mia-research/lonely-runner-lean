"""
lrc_gap_deep_v1.py
==================
Deep investigation: for each in-range (n, L, d) case in A.5/A.4,
  1. Show exact safe fibres and their mechanisms for canonical tuples
  2. Search NON-CANONICAL tuples (different speed representatives, same residues mod n)
     to find the true minimum x0 across ALL valid small-L tuples
  3. Classify mechanisms for the hardest (minimum x0) cases
"""
import sys, math, itertools
from fractions import Fraction
from collections import defaultdict

def euler_phi(n):
    r, t = n, n
    p = 2
    while p*p <= t:
        if t%p==0:
            while t%p==0: t//=p
            r -= r//p
        p+=1
    if t>1: r-=r//t
    return r

def extended_gcd(a,b):
    if a==0: return b,0,1
    g,x,y = extended_gcd(b%a,a); return g, y-(b//a)*x, x

def mod_inv(a,n):
    g,x,_=extended_gcd(a%n,n); assert g==1; return x%n

def lcm_list(lst):
    r=1
    for x in lst: r=math.lcm(r,x)
    return r

def is_prime(n):
    if n<2: return False
    for p in range(2,int(n**0.5)+1):
        if n%p==0: return False
    return True

def x0_count(E_full, n):
    """Fast x0 computation: count k in {0,...,N-1} with L<=e*k mod N<=(n-1)*L for all e."""
    L = lcm_list(E_full)
    N = n*L
    lo,hi = L,(n-1)*L
    return sum(1 for k in range(N) if all(lo<=(e*k)%N<=hi for e in E_full)), L

def x0_classified(E_full, n, d):
    """x0 with mechanism classification for each safe fibre."""
    L = lcm_list(E_full)
    N = n*L
    lo,hi = L,(n-1)*L
    d_inv = mod_inv(d,n)
    r_d   = (-d_inv)%n
    s_d   = (d_inv-1)%n
    I_lo  = Fraction(L,n);     I_hi=Fraction(L,n-1)
    J_lo  = Fraction((n-2)*L,n-1); J_hi=Fraction((n-1)*L,n)

    reset_map = {}
    for e in E_full:
        if math.gcd(e,n)!=1: continue
        for m in range(1,e):
            if (m*L)%e==0: reset_map[(m*L)//e]=(e,m)

    safe=[]
    for k in range(N):
        if not all(lo<=(e*k)%N<=hi for e in E_full): continue
        bf=Fraction(k)
        if I_lo<=bf<I_hi:
            mech="SOLE_COVER"
        elif J_lo<=bf<=J_hi:
            mech="DUAL_SOLE"
        elif k in reset_map:
            mech="FLOOR_RESET"
        else:
            mech="OTHER"
        safe.append((k,mech))
    return len(safe),safe,L

# ── enumerate ALL small-L tuples for (n, d) ────────────────────────────────

def enumerate_all_small_L(n, d, threshold):
    """
    Enumerate ALL tuples E = E_non ∪ {e_div} with:
      - e_div ≡ 0 mod n (divisible runner)
      - E_non: one runner per residue class in {1,...,n-1} \ {d}
      - gcd(E) = 1
      - lcm(E) < threshold
    Each runner speed e_r ≡ r (mod n) with e_r ≥ 1 and e_r < threshold.
    """
    residue_classes = [r for r in range(1,n) if r != d]  # n-2 residue classes
    # For each class, list candidate speeds < threshold
    candidates = {r: list(range(r, threshold, n)) for r in residue_classes}
    div_candidates = list(range(n, threshold, n))  # divisible runner speeds

    results = []

    for e_div in div_candidates:
        # Iterate over one representative per residue class
        def recurse(classes, current):
            if not classes:
                E = current + [e_div]
                if math.gcd(*E) != 1: return
                L = lcm_list(E)
                if L >= threshold or L <= 2*n: return
                results.append((L, tuple(sorted(E))))
                return
            r = classes[0]
            for e_r in candidates[r]:
                if lcm_list(current + [e_r]) >= threshold: break  # prune
                recurse(classes[1:], current + [e_r])

        recurse(residue_classes, [])

    # Deduplicate (same tuple can appear from different orderings — but sorted handles that)
    unique = {}
    for L, E in results:
        if E not in unique: unique[E] = L
    return [(L, list(E)) for E, L in unique.items()]

# ── main analysis ────────────────────────────────────────────────────────────

def analyse_A5():
    print("\n"+"="*72)
    print("A.5 DEEP INVESTIGATION  (ALL small-L tuples, not just canonical)")
    print("="*72)

    composite_ns = [n for n in range(4,13) if not is_prime(n)]

    for n in composite_ns:
        phi_n  = euler_phi(n)
        thresh = n*(n-1)*(phi_n//2+1)
        units  = [a for a in range(1,n) if math.gcd(a,n)==1]
        print(f"\n── n={n}  φ={phi_n}  threshold L<{thresh} ──")

        all_cases = []
        min_x0_overall = float('inf')
        hardest_cases = []

        for d in units:
            tuples = enumerate_all_small_L(n, d, thresh)
            for L, E in tuples:
                x0, L2 = x0_count(E, n)
                all_cases.append((x0, L, d, E))
                if x0 < phi_n:
                    print(f"  *** FAILURE x0={x0}<phi={phi_n}  d={d}  E={E}  L={L}")
                if x0 < min_x0_overall:
                    min_x0_overall = x0
                    hardest_cases = [(x0, L, d, E)]
                elif x0 == min_x0_overall:
                    hardest_cases.append((x0, L, d, E))

        if not all_cases:
            print("  no cases in range")
            continue

        x0_vals = [c[0] for c in all_cases]
        fails = sum(1 for x in x0_vals if x < phi_n)
        print(f"  total tuples: {len(all_cases)}  fails: {fails}  "
              f"x0∈[{min(x0_vals)},{max(x0_vals)}]  min_x0={min_x0_overall}")

        print(f"\n  HARDEST CASES (min x0={min_x0_overall}) — detailed mechanism breakdown:")
        seen = set()
        for (x0, L, d, E) in hardest_cases[:10]:  # show at most 10
            key = (tuple(sorted(E)), d)
            if key in seen: continue
            seen.add(key)
            _, safe_list, _ = x0_classified(E, n, d)
            mech_counts = defaultdict(int)
            for (k,m) in safe_list: mech_counts[m]+=1
            print(f"    n={n} L={L} d={d} E={sorted(E)}  x0={x0}")
            print(f"      mechanisms: {dict(mech_counts)}")
            if len(safe_list) <= 20:
                for (k,m) in safe_list:
                    I_lo=Fraction(L,n); I_hi=Fraction(L,n-1)
                    J_lo=Fraction((n-2)*L,n-1); J_hi=Fraction((n-1)*L,n)
                    bf=Fraction(k)
                    note = ""
                    if I_lo<=bf<I_hi: note=f" [I_d=({I_lo},{I_hi})]"
                    elif J_lo<=bf<=J_hi: note=f" [J=({J_lo},{J_hi})]"
                    print(f"      k={k}  {m}{note}")

if __name__ == "__main__":
    analyse_A5()
