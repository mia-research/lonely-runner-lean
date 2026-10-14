"""modgap_hard_v1 (2026-10-06): the (6,1) first-component statement on the record's hard sets (rule 10: arrangements the statement was not built on).  Hard sets: the 28 sets read from
order5_transfer_v1.out (the 28 hard sets of the [1,40] residual, as fast_pair_constant_v1.py reads them), and hard_sets_41_60.json.  These are the sets on which every uniform lower-order bound
examined in MANUSCRIPT_v22 section 17E fails (fast pair with uniform cell constant: 0 of 28).  Per set: k_d for every d, the set D1 of good d at the first component, rules B (argmax t_d) and D (soonest
edge), the interval criterion R(d) = 4 d (r - l) >= 1, and the set's own 1/8 landing t*.  Exact."""
import sys, re, json, collections
sys.path.insert(0, '.')
_src = open('modgap_rule_d_v1.py').read()
_src = _src.replace("out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("rules = {")[0])
from modgap_lib_v1 import cascade as casc8
hard = sorted({tuple(map(int, m.group(1).split(','))) for m in
               (re.match(r'\s*\(([\d, ]+)\):', l) for l in open('../order5_transfer_v1.out')) if m})
hard = [h for h in hard if len(h) == 7]
j = json.load(open('../hard_sets_41_60.json'))
h2 = []
def walk(x):
    if isinstance(x, list) and x and all(isinstance(v, int) for v in x) and len(x) == 7: h2.append(tuple(sorted(x)))
    elif isinstance(x, list):
        for v in x: walk(v)
    elif isinstance(x, dict):
        for v in x.values(): walk(v)
walk(j); h2 = sorted(set(h2))
out = open('modgap_hard_v1.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('28 hard sets of the [1,40] residual', hard), ('hard_sets_41_60.json', h2)):
    c = collections.Counter(); rows = []
    for S in sets:
        I = [info(S, d) for d in S]; t8 = casc8(S)
        good = [x['d'] for x in I if x['good']]
        dstar = max(I, key=lambda x: (x['t'], x['d'])); dD = min(I, key=lambda x: (x['edge'], -x['d']))
        c['some d good at first component'] += bool(good); c['rule B good'] += dstar['good']; c['rule D good'] += dD['good']
        c['some d with R >= 1 (interval criterion)'] += any(x['R'] >= 1 for x in I)
        c[('number good', len(good))] += 1
        rows.append((S, good, dstar['d'], dD['d'], str(t8)))
    out.write("\n==== %s: %d sets\n" % (name, len(sets)))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    for r in rows[:30]: out.write("  S=%s good d=%s; rule B picks %d; rule D picks %d; t*=%s\n" % r)
out.close(); print(open('modgap_hard_v1.out').read()[len(__doc__):][:5200])
