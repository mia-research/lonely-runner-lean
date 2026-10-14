"""modgap_rule_d_v2 (2026-10-06): why rule B (d* = argmax_d t_d) works.  t* = S's own first lonely instant at 1/8 (the cascade of the framework).  For d*: its first 1/7-component C(d*) = [l, r], l = t_{d*}.
Recorded per population: position of t* against [l, r] (t* < l, l <= t* <= r, t* > r); whether t* = max_d t_d, t* <= max_d t_d, t* >= min_d t_d; whether d* is S's opener or closer at t*; the failures of rule B
(sets where d* is not good) listed individually with t*, t_d for all d, and the component of d*.  Exact."""
import sys, collections
sys.path.insert(0, '.')
_src = open('modgap_rule_d_v1.py').read()
_src = _src.replace("out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("rules = {")[0])
from modgap_lib_v1 import cascade as casc8, openers, component
out = open('modgap_rule_d_v2.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1 [:1500]', T1[:1500])):
    c = collections.Counter(); fails = []; n = 0
    for S in sets:
        n += 1; I = [info(S, d) for d in S]; ts = {x['d']: x['t'] for x in I}
        dstar = max(I, key=lambda x: (x['t'], x['d'])); t8 = casc8(S)
        op = openers(S, t8); tR, cl = component(S, t8)
        pos = 'before l' if t8 < dstar['l'] else ('inside [l, r]' if t8 <= dstar['r'] else 'after r')
        c[('t* vs C(d*)', pos)] += 1
        c[('t* <= max t_d', t8 <= dstar['t'])] += 1; c[('t* = max t_d', t8 == dstar['t'])] += 1; c[('t* >= min t_d', t8 >= min(ts.values()))] += 1
        c[('d* is the opener at t*', dstar['d'] in op)] += 1; c[('d* is the closer at t*', dstar['d'] in cl)] += 1
        c[('d* good', dstar['good'])] += 1
        if not dstar['good'] and len(fails) < 12: fails.append((S if len(str(S[-1])) < 12 else '[%d-digit] first %s' % (len(str(S[-1])), str(S[0])[:10]), str(t8)[:30], dstar['d'] if len(str(dstar['d'])) < 12 else '[d*]', str(dstar['l'])[:20], str(dstar['r'])[:20]))
    out.write("\n==== %s: %d sets\n" % (name, n))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    for f in fails: out.write("  rule B fails: %s\n" % (f,))
out.close(); print(open('modgap_rule_d_v2.out').read()[len(__doc__):][:6000])
