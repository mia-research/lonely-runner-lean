"""modgap_open_v2 (2026-10-06): the open class of modgap_open_v1 by the record's pattern (number of multiples of 8, type of the non-multiples), with the extremes per pattern, and the
step-by-step path of the eight open members with the largest laps traversed in one jump.  Exact."""
import sys, math, collections
sys.path.insert(0, '.')
exec(open('modgap_open_v1.py').read().split("out = open('modgap_open_v1.out'")[0])
from fractions import Fraction as F
def pat(S):
    return (sum(1 for d in S if d % 8 == 0), typ([d % 8 for d in S if d % 8]))
out = open('modgap_open_v2.out', 'w'); out.write(__doc__ + "\n")
allm = [(n, S) for n, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1', T1)) for S in sets]
byp = collections.defaultdict(list)
for n, S in allm:
    if cls(S) == 'open': byp[pat(S)].append((n, S))
out.write("open members by pattern (multiples of 8, type of the non-multiples; f = 4 mod 8, t = 2 mod 4, o = odd): count, max laps in one jump, max re-blocks, sources\n")
stats = {}
for p, L in sorted(byp.items(), key=lambda kv: -len(kv[1])):
    mw = 0; mr = 0; srcs = collections.Counter(n for n, _ in L)
    for n, S in L:
        path = cascade_path(S); ts = [q for q, _ in path]; seen = {}; rb = 0
        for i, ti in enumerate(ts):
            for d in S:
                if cd(d * ti) < E8:
                    if d in seen and seen[d] != i: rb += 1
                    seen[d] = i
            if i + 1 < len(ts): mw = max(mw, max(math.floor(d * (ts[i + 1] - ti)) for d in S))
        mr = max(mr, rb)
    out.write("  %s: %d members, max laps %d, max re-blocks %d, sources %s\n" % (p, len(L), mw, mr, dict(srcs)))
# the eight extreme-wrap members
ext = []
for n, S in allm:
    if cls(S) != 'open': continue
    path = cascade_path(S); ts = [q for q, _ in path]
    w = max(math.floor(d * (ts[i + 1] - ts[i])) for i in range(len(ts) - 1) for d in S) if len(ts) > 1 else 0
    ext.append((w, n, S))
ext.sort(key=lambda x: -x[0])
out.write("\nthe eight open members with the largest laps traversed in one jump (path: state index, setter's size in digits, jump length as an exact fraction of t*, and for each jump the reading that traverses the most laps with its lap count):\n")
for w, n, S in ext[:8]:
    path = cascade_path(S); ts = [q for q, _ in path]; t = ts[-1]
    out.write("  [%s] %d-digit readings; d_min = %s; ratio d_max/d_min ~ 10^%d; moves %d; max laps %d; pattern %s\n" % (n, len(str(S[-1])), str(S[0])[:14] + '...', len(str(S[-1])) - len(str(S[0])), len(ts) - 1, w, pat(S)))
    for i in range(len(ts) - 1):
        dt = ts[i + 1] - ts[i]; d_best = max(S, key=lambda d: d * dt)
        out.write("     step %d -> %d: setter %s... (%d digits); the reading with most laps: %s... (%d digits) traverses %d laps; jump/t* = %.3e\n" %
                  (i, i + 1, str(path[i + 1][1])[:10], len(str(path[i + 1][1])), str(d_best)[:10], len(str(d_best)), math.floor(d_best * dt), float(dt / t)))
out.close(); print(open('modgap_open_v2.out').read()[len(__doc__):][:7500])
