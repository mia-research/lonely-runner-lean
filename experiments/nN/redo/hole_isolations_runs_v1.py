"""E241 (2026-10-01): read off the isolation record (hole_isolations_f<f>_v1.jsonl.gz): runs of consecutive core
stretches in (0, 1/2] that hold no isolation.

Lead read from hole_isolations_v1.out: in the first ten stretches a stretch holding none is almost always alone.  Here,
over every stretch in (0, 1/2] of every configuration: the longest run of consecutive stretches holding none, by f; every
run of two or more listed with its configuration and stretch indices.  The last stretch is cut at 1/2 (its mirror
continues it), so a run ending at the cut is marked.
"""
import json, gzip
from collections import Counter

out = open('hole_isolations_runs_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
for f in (3, 4, 5, 6):
    longest = Counter(); runs2 = []; nstretch = 0; nnone = 0
    for line in gzip.open('hole_isolations_f%d_v1.jsonl.gz' % f, 'rt'):
        r = json.loads(line); st = r['st']; nstretch += len(st)
        best = cur = 0; start = None
        for k, row in enumerate(st):
            if not row[4]:
                nnone += 1
                if cur == 0:
                    start = k
                cur += 1; best = max(best, cur)
                if cur >= 2 and (not runs2 or runs2[-1][0] != r['S'] or runs2[-1][1] != start):
                    runs2.append((r['S'], start))
            else:
                cur = 0
        longest[best] += 1
    w("\n== f = %d: %d stretches, %d holding none ==" % (f, nstretch, nnone))
    w("  configurations by their longest run of consecutive stretches holding none: %s" % dict(sorted(longest.items())))
    w("  runs of two or more (%d), first 20: %s" % (len(runs2), runs2[:20]))
out.close()
print(open('hole_isolations_runs_v1.out').read()[len(__doc__):])
