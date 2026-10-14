"""modgap_family_v3 (2026-10-06): does a single odd reading set the instant at most once?  On the (3, oooo) members: the new family of modgap_family_v2 (K = 2, 6, 12, 18, 24, 27, same
seeds and draws) and the stored DA, DB.  Per member: the number of times each reading is the setter along the cascade path; reported: the maximum for odd readings, the maximum for
multiples of 8, the distribution of the number of odd setter events and of multiple setter events.  If an odd reading sets at most once, the number of odd setter events is at most 4 and the
alternation count is at most 2 * 4 + ... (bounded by the reading count), which is a reading of the data, not a proof.  Exact."""
import sys, json, collections, random
sys.path.insert(0, '.')
exec(open('modgap_family_v2.py').read().split("out = open('modgap_family_v2.out'")[0])
out = open('modgap_family_v3.out', 'w'); out.write(__doc__ + "\n")
def stats(name, sets):
    mo = mm = 0; od = collections.Counter(); md = collections.Counter(); both = collections.Counter()
    for S in sets:
        path = cascade_path(S); setters = [d for _, d in path[1:]]
        c = collections.Counter(setters)
        mo = max([mo] + [v for d, v in c.items() if d % 8]); mm = max([mm] + [v for d, v in c.items() if d % 8 == 0])
        od[sum(v for d, v in c.items() if d % 8)] += 1; md[sum(v for d, v in c.items() if d % 8 == 0)] += 1
    out.write("%s: %d members; max times one odd reading sets: %d; max times one multiple sets: %d; odd setter events %s; multiple setter events %s\n" %
              (name, len(sets), mo, mm, dict(sorted(od.items())), dict(sorted(md.items()))))
st = json.load(open('divisible_members_v2.json'))
for nm in ('A', 'B'): stats('stored %s' % nm, [tuple(sorted(S)) for S in st[nm]])
for K in (2, 6, 12, 18, 24, 27):
    rnd = random.Random(20261006 + K); mem = []; tried = 0
    while tried < 60000 and len(mem) < 1500:
        tried += 1
        S = build(rnd, K, 1)
        if S is not None and full_residual(S): mem.append(S)
    mem = list(dict.fromkeys(mem)); stats('new K = %d' % K, mem)
out.close(); print(open('modgap_family_v3.out').read()[len(__doc__):])
