"""Divisor-closed profiles: is A = c*m + 1 always a witness, for an R-like multiplier c?

Derivation: s_i | m, so b_i = m/s_i and blocks(s_i,A,m) <-> blocks(1,A,b_i).
With A = c*m+1:  A mod 8 b_i = b_i * (c * s_i mod 8) + 1.
That lies in [b_i, 7 b_i]  iff  c * s_i mod 8 in [1,6]   (for b_i >= 2; b_i = 1 is free).
Need also A = 1 mod 8  (so 8 | c*m)  and  A <= 7m  (so c <= 6).
"""
from itertools import combinations

def clear_at(S, sk):
    M = 8*sk; A = sk + ((1-sk) % 8)
    while A <= 7*sk:
        if all(min((si*A) % M, M - (si*A) % M) >= sk for si in S): return A
        A += 8
    return None

def c_witness(S, m):
    """Least c in [1,6] with 8 | c*m and c*s_i mod 8 in [1,6] for every s_i != m."""
    for c in range(1, 7):
        if (c*m) % 8: continue
        if all(1 <= (c*si) % 8 <= 6 for si in S if si != m): return c
    return None

tot = no_c = mismatch = 0; exs = []
for m in range(24, 900):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for comb in combinations(mid, 5):
        S = (1,) + comb + (m,)
        tot += 1
        c = c_witness(S, m)
        if c is None:
            no_c += 1
            if len(exs) < 4: exs.append(("no c", S))
        else:
            A = c*m + 1
            M = 8*m
            ok = all(min((si*A) % M, M - (si*A) % M) >= m for si in S)
            if not ok:
                mismatch += 1
                if len(exs) < 4: exs.append(("c bad", S, c))
print(f"divisor-closed, exhaustive m < 900 : {tot:,} profiles")
print(f"  no admissible c in [1,6]         : {no_c:,}")
print(f"  c found but A = c*m+1 NOT clear  : {mismatch:,}   (derivation says 0)")
for e in exs: print("     ", e)

# if c always exists, WHICH c?
from collections import Counter
cc = Counter()
for m in range(24, 400):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for comb in combinations(mid, 5):
        S = (1,) + comb + (m,)
        cc[c_witness(S, m)] += 1
print(f"\n  least admissible c: {dict(sorted(cc.items(), key=lambda kv:(kv[0] is None, kv[0])))}")
