"""s = s* is refuted.  reach_mem only promises SOME right endpoint.  Which reading supplies it?"""
from itertools import combinations
from collections import Counter

def W(S, s):
    M, out = 8*s, []
    A = s + ((1 - s) % 8)
    while A <= 7*s:
        if all(min((sp*A) % M, M - (sp*A) % M) >= s for sp in S):
            out.append(A)
        A += 8
    return out

def lonely_any(S):
    """Which s in S supply a witness?  Returns the list of working s."""
    return [s for s in S if W(S, s)]

no_wit, tot = [], 0
who = Counter(); rank = Counter(); nwork = Counter()
for combo in combinations(range(2, 31), 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo
    tot += 1
    good = lonely_any(S)
    nwork[len(good)] += 1
    if not good:
        no_wit.append(S)
    else:
        Ss = sorted(S)
        who[min(good)] += 1
        rank[Ss.index(min(good))] += 1

print(f"Branch B profiles (6 free readings from [2,30], a multiple of 8 present): {tot:,}")
print(f"  profiles with NO witness at ANY s in S: {len(no_wit):,}")
if no_wit:
    for S in no_wit[:8]: print("    ", S)
print(f"\n  how many readings supply a witness: {dict(sorted(nwork.items()))}")
print(f"\n  SMALLEST working reading s, by value (top 12):")
for v, c in who.most_common(12):
    print(f"     s = {v:>3}  in {c:>7,} profiles  ({100*c/tot:5.2f}%)   "
          f"{'ODD' if v%2 else 'even'}  v2={(v & -v).bit_length()-1}")
print(f"\n  its RANK in the sorted profile (0 = smallest reading): {dict(sorted(rank.items()))}")
