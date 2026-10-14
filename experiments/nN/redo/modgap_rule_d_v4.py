"""modgap_rule_d_v4 (2026-10-06): test 'good(d) iff t_d > t*' where t_d is the first 1/7-lonely instant of S minus d, t* S's own first 1/8-lonely instant (the framework's cascade), and good(d) means d has a
point at distance >= 1/8 inside the first component of S minus d at 1/7 (clear_in_interval_iff).  Also: the same with the whole 1/7 lonely set: does d clear at SOME instant of L_7(S minus d) lying after t*?
Per (set, d): the four cells of (t_d > t*) x good(d), and for the cell (t_d <= t*, good) and (t_d > t*, not good) the individual cases.  [P] for t_d <= t* and r_d <= t*: not good (S is not 1/8-lonely before t*, and the others
are clear on the component).  Exact."""
import sys, collections
sys.path.insert(0, '.')
_src = open('modgap_rule_d_v1.py').read()
_src = _src.replace("out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("rules = {")[0])
from modgap_lib_v1 import cascade as casc8
out = open('modgap_rule_d_v4.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1 [:1500]', T1[:1500])):
    c = collections.Counter(); ex = []
    for S in sets:
        t8 = casc8(S)
        for d in S:
            x = info(S, d)
            cell = ('t_d > t*' if x['t'] > t8 else 't_d <= t*', 'good' if x['good'] else 'bad')
            c[cell] += 1
            if x['t'] <= t8:
                c[('t_d <= t*: component ends before t* (r_d <= t*)', x['r'] <= t8, 'good' if x['good'] else 'bad')] += 1
            if x['t'] > t8 and not x['good'] and len(ex) < 6: ex.append((S if len(str(S[-1])) < 12 else '[%d-digit]' % len(str(S[-1])), d if len(str(d)) < 12 else '[d]', str(x['t'])[:22], str(t8)[:22], str(x['r'])[:22], float(x['R'])))
    out.write("\n==== %s\n" % name)
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    for e in ex: out.write("  (t_d > t*, d bad): %s\n" % (e,))
out.close(); print(open('modgap_rule_d_v4.out').read()[len(__doc__):][:5000])
