"""E264 (2026-10-02): Part 3 of restricted_b_v1.py run on its own (the combined run's pool stopped after Parts 1-2; Parts 1-2's
output is in restricted_b_v1.out).  Same functions (restricted_b_v1.part3_shape), same seeds (3000 + shape index).  Design: log E263."""
import sys, os
from collections import Counter
from multiprocessing import Pool
import restricted_b_v1 as R

if __name__ == '__main__':
    P58 = R.parse58()
    out = open('restricted_b_p3_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    res = {}
    with Pool(8) as pool:
        for i, r in enumerate(pool.imap_unordered(R.part3_shape, [(i, six, 3000 + i) for i, (six, K) in enumerate(P58)])):
            res[r['six']] = r
            print('done', i + 1, flush=True)
    P3 = [res[six] for six, K in P58]
    w("PART 3: %d shapes, c = L*u, cluster K*six + integer adjustments, 6 restarts x 400 steps, 16 predicates" % len(P3))
    w("  CHECK start states violating the constraint: %d of %d" % (sum(1 for s in P3 for r in s['runs'] if not r['start_ok']), 6 * len(P3)))
    for tag, name in (('C', 'CONSTRAINED (fastest flank stays a hand-off)'), ('U', 'CONTROL (no constraint)')):
        mem = [(s['six'], r) for s in P3 for r in s['runs'] if r[tag]['member']]
        w("  %s: members reached %d of %d runs; shapes with a member %d of %d" % (name, len(mem), 6 * len(P3), len({six for six, r in mem}), len(P3)))
        ck = Counter(); lo_bad = 0
        for six, r in mem:
            ck.update(r[tag]['study']['chk']); lo_bad += (not r[tag]['study']['land_ok'])
        w("    members' CHECKS: %s; landing not earliest first-clear cluster flank: %d" % (dict(ck) if ck else '0 failures', lo_bad))
        w("    fastest-flank state at the end: %s" % dict(Counter(r[tag]['fast'] for s in P3 for r in s['runs'])))
        w("    members' fastest-flank state: %s" % dict(Counter(r[tag]['fast'] for six, r in mem)))
        best = Counter()
        for s in P3:
            b = min(s['runs'], key=lambda r: len(r[tag]['fail']))
            best[tuple(b[tag]['fail'])] += 1
        w("    best run per shape, fields still failing: %s" % best.most_common(12))
        fc = Counter()
        for s in P3:
            for r in s['runs']: fc.update(r[tag]['fail'])
        w("    field failure counts over all %d final states: %s" % (6 * len(P3), {n: fc.get(n, 0) for n in R.NAMES}))
        w("    final scores (fields passed of 16): %s" % dict(sorted(Counter(r[tag]['score'] for s in P3 for r in s['runs']).items())))
        for six, r in mem[:10]:
            w("    member from six %s: %s" % (six, r[tag]['study']['T']))
    out.close(); print(open('restricted_b_p3_v1.out').read()[len(__doc__):])
