"""modgap_dmin_perturb_v1 (2026-10-06): test of the mechanism 'no good d at the first 1/7-component only when d_min = 0 mod 8'.  Perturbation: S' = S with d_min replaced by d_min + j, j in {-7..7} minus 0, and
j in {-16, -8, 8, 16} (the multiples of 8 keep the class).  good(d) = d has a point >= 1/8 inside the first 1/7-component of S' minus d (clear_in_interval_iff, exact).  Groups: (E) the 9 exceptions found in
modgap_nogood_v1.out and hard_sets_41_60 (every set with no good d at component 1), (K) a seeded sample of 800 members of T1 with d_min = 0 mod 8 that were NOT exceptions.  For each group and each class of the new d_min
(0 mod 8 or not): the number of variants, how many have no good d at component 1, and (for E) the exact list of the variants of each exception that fail.  Duplicates among readings or an order change are re-sorted;
variants with a repeated reading are skipped.  Seeded random.Random(20261006).  Exact."""
import sys, json, random, collections, re
sys.path.insert(0, '.')
_src = open('modgap_rule_d_v1.py').read()
_src = _src.replace("out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("rules = {")[0])
hard = []
h2 = []
def wk(x):
    if isinstance(x, list) and x and all(isinstance(v, int) for v in x) and len(x) == 7: h2.append(tuple(sorted(x)))
    elif isinstance(x, list):
        for v in x: wk(v)
    elif isinstance(x, dict):
        for v in x.values(): wk(v)
wk(json.load(open('../hard_sets_41_60.json'))); h2 = sorted(set(h2))
def nogood(S): return not any(info(S, d)['good'] for d in S)
exc = []
for S in T1 + h2:
    if S[0] % 8 == 0 and nogood(S): exc.append(S)
rnd = random.Random(20261006)
pool = [S for S in T1 if S[0] % 8 == 0 and S not in set(exc)]
ctl = rnd.sample(pool, 800)
JS = [j for j in range(-7, 8) if j] + [-16, -8, 8, 16]
out = open('modgap_dmin_perturb_v1.out', 'w'); out.write(__doc__ + "\n")
out.write("exceptions found (no good d at component 1, d_min = 0 mod 8): %d\n" % len(exc))
for name, group in (('E: the exceptions', exc), ('K: control sample of non-exceptions with d_min = 0 mod 8', ctl)):
    c = collections.Counter(); fails = collections.defaultdict(list)
    for S in group:
        for j in JS:
            nd = S[0] + j
            if nd <= 0 or nd in S: continue
            S2 = tuple(sorted((nd,) + S[1:]))
            cls = 'new d_min = 0 mod 8' if S2[0] % 8 == 0 else 'new d_min not 0 mod 8'
            if S2[0] != nd: cls += ' (order changed)'
            c[(cls, 'variants')] += 1
            if nogood(S2):
                c[(cls, 'no good d at component 1')] += 1
                if group is exc: fails[S].append(j)
    out.write("\n==== %s: %d sets\n" % (name, len(group)))
    for k, v in sorted(c.items()): out.write("  %s: %s: %d\n" % (k[0], k[1], v))
    for S, js in fails.items(): out.write("  exception %d-digit: variants that still fail, j = %s\n" % (len(str(S[-1])), sorted(js)))
out.close(); print(open('modgap_dmin_perturb_v1.out').read()[len(__doc__):])
