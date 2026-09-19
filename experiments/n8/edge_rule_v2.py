"""v1 reported 'always smallest modulus, always L' -- that was my enumeration order.
Measure ALL (b, end) pairs that supply a witness, and test each as a STANDALONE rule."""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs): return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])

def supplies(m, bs, b, e):
    """Does the residue class q = e (mod b) contain a witness?"""
    q = e % b
    while q < m:
        if ok(q, m, bs): return True
        q += b
    return False

tot = 0; miss = 0
cnt = Counter(); rank_any = Counter(); end_any = Counter()
rules = Counter()
for m in range(24, 240):
    ds = [d for d in range(2, m) if m % d == 0]
    if len(ds) < 5: continue
    for c in combinations(ds, 5):
        bs = sorted(c)
        if not any(ok(q, m, bs) for q in range(m)): continue
        tot += 1
        allb = bs + [m]
        good = []
        for i, b in enumerate(sorted(allb)):
            L, U = I(b)
            for lab, e in (('L', L), ('U', U)):
                if supplies(m, bs, b, e):
                    good.append((i, b, lab))
        if not good: miss += 1; continue
        cnt[len(good)] += 1
        for i, b, lab in good:
            rank_any[i] += 1; end_any[lab] += 1
        # standalone rules
        ranks = {i for i,_,_ in good}; ends = {lab for _,_,lab in good}
        rules['smallest modulus works'] += (0 in ranks)
        rules['largest modulus works'] += (5 in ranks)
        rules['L end works (some b)'] += ('L' in ends)
        rules['U end works (some b)'] += ('U' in ends)
print(f"profiles {tot:,}   no edge witness {miss:,}\n")
print(f"  how many (b,end) pairs supply a witness: "
      + "  ".join(f"{k}:{100*v/tot:.1f}%" for k,v in sorted(cnt.items())))
s = sum(rank_any.values())
print(f"  supplying modulus by rank (0=smallest of six): "
      + "  ".join(f"{k}:{100*v/s:.1f}%" for k,v in sorted(rank_any.items())))
print(f"  supplying end: L {100*end_any['L']/max(sum(end_any.values()),1):.1f}%  "
      f"U {100*end_any['U']/max(sum(end_any.values()),1):.1f}%")
print()
for k, v in rules.items():
    print(f"  rule '{k:<24}' holds for {100*v/tot:6.2f}% of profiles"
          + ("   <-- 100%" if v == tot else ""))
