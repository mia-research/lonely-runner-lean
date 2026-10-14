"""modgap_nogood_v1 (2026-10-06): the members with no good d at the first 1/7-component of S minus d (good: d has a point >= 1/8 inside the component, clear_in_interval_iff).  Over ALL stored members
(C 547, BS 287, DA 41, DB 371, T1 5,431).  For each such set: classes mod 8 in size order, k_d per reading (first component index with a clear point for d, cap 40), the 1/7-landing of S itself (index of the first
shell/lonely state of the full walk), whether the first-component widths R7(d) = (7d/2) width are all < 1, and which readings are multiples of 8.  Exact."""
import sys, json, collections
sys.path.insert(0, '.')
_src = open('modgap_rule_d_v1.py').read()
_src = _src.replace("out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("rules = {")[0])
from modgap_lib_v1 import typ8
out = open('modgap_nogood_v1.out', 'w'); out.write(__doc__ + "\n")
tot = 0; rows = []
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1', T1)):
    n = 0; ng = 0
    for S in sets:
        n += 1
        I = [info(S, d) for d in S]
        if not any(x['good'] for x in I):
            ng += 1
            ks = [kd(S, d, 40) for d in S]
            rows.append((name, S, ''.join(typ8(d) for d in S), ks, [str(F(7 * d, 2) * (x['r'] - x['l']))[:10] for d, x in zip(S, I)]))
    out.write("%s: %d members; no good d at the first component: %d\n" % (name, n, ng))
out.write("\n")
for name, S, cls, ks, R in rows:
    out.write("[%s] %d-digit readings; classes %s; k_d %s; multiples of 8: %d; all R7(d) < 1 at the first component: %s\n" %
              (name, len(str(S[-1])), cls, ks, sum(1 for d in S if d % 8 == 0), all(F(7 * d, 2) * (x['r'] - x['l']) < 1 for d, x in zip(S, [info(S, d) for d in S]))))
out.close(); print(open('modgap_nogood_v1.out').read()[len(__doc__):][:4500])
