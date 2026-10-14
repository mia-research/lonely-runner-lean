"""modgap_nogood_v2 (2026-10-06): is 'no good d at the first component' tied to d_min being a multiple of 8?  Over all stored members (C, BS, DA, DB, T1 5,431) and the hard sets: for each class of d_min (mod 8), the number of
sets, the number with no good d at the first component, and the number with no good d within the first two components.  Exact."""
import sys, collections
sys.path.insert(0, '.')
_src = open('modgap_rule_d_v1.py').read()
_src = _src.replace("out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("rules = {")[0])
import re, json
hard = sorted({tuple(map(int, m.group(1).split(','))) for m in (re.match(r'\s*\(([\d, ]+)\):', l) for l in open('../order5_transfer_v1.out')) if m}); hard = [h for h in hard if len(h) == 7]
h2 = []
def wk(x):
    if isinstance(x, list) and x and all(isinstance(v, int) for v in x) and len(x) == 7: h2.append(tuple(sorted(x)))
    elif isinstance(x, list):
        for v in x: wk(v)
    elif isinstance(x, dict):
        for v in x.values(): wk(v)
wk(json.load(open('../hard_sets_41_60.json'))); h2 = sorted(set(h2))
out = open('modgap_nogood_v2.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1', T1), ('28 hard', hard), ('hard 41-60', h2)):
    c = collections.Counter()
    for S in sets:
        cls = 'm' if S[0] % 8 == 0 else ('o' if S[0] % 2 else ('t' if S[0] % 4 == 2 else 'f'))
        ks = [kd(S, d, 3) for d in S]
        c[(cls, 'sets')] += 1
        c[(cls, 'no good d at component 1')] += not any(k == 1 for k in ks)
        c[(cls, 'no good d within components 1-2')] += not any(k in (1, 2) for k in ks)
    out.write("\n==== %s: %d sets\n" % (name, len(sets)))
    for k, v in sorted(c.items()): out.write("  d_min class %s, %s: %d\n" % (k[0], k[1], v))
out.close(); print(open('modgap_nogood_v2.out').read()[len(__doc__):])
