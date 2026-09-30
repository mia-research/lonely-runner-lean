"""E194b: minimal covering sub-multisets ("cores") of the 32,642 exceptional m = 1 patterns (crowded_m1_cover_v1).
A pattern has no lonely a/64 iff some sub-multiset of its residues blocks all 56 instants.  Cores are the minimal such
sub-multisets, in canonical form under the unit group mod 64 (least sorted tuple over the 32 unit multiples)."""
import itertools
from collections import Counter
A = [a for a in range(1, 64) if a % 8]
FULL = (1 << len(A)) - 1
B = [sum(1 << i for i, a in enumerate(A) if not (8 <= (a * x) % 64 <= 56)) for x in range(64)]
def canon(t):
    return min(tuple(sorted((u * x) % 64 for x in t)) for u in range(1, 64, 2))
pats = [tuple(map(int, l.split())) for l in open('crowded_m1_cover_v1.patterns')]
cores = Counter(); size = Counter(); per = []
for p in pats:
    idx = range(7); found = []
    for k in range(1, 8):
        for c in itertools.combinations(idx, k):
            m = 0
            for i in c: m |= B[p[i]]
            if m == FULL and not any(set(f) <= set(c) for f in found):
                found.append(c)
        if found and k >= max(len(f) for f in found) + 0:
            pass
    mins = [f for f in found if not any(set(g) < set(f) for g in found)]
    cs = {canon([p[i] for i in f]) for f in mins}
    for c in cs: cores[c] += 1
    size[min(len(f) for f in mins)] += 1
out = open('crowded_m1_cores_v1.out', 'w')
out.write(__doc__ + "\n")
out.write("patterns: %d\nsmallest core size per pattern: %s\ndistinct cores (canonical): %d\n" % (len(pats), dict(sorted(size.items())), len(cores)))
bysize = Counter(len(c) for c in cores)
out.write("cores by size: %s\n" % dict(sorted(bysize.items())))
for c, n in sorted(cores.items(), key=lambda kv: (len(kv[0]), -kv[1]))[:80]:
    out.write("  core %s in %d patterns; residues mod 8 %s; mod 16 %s\n" % (c, n, [x % 8 for x in c], [x % 16 for x in c]))
out.close()
print(open('crowded_m1_cores_v1.out').read()[len(__doc__):][:6000])
