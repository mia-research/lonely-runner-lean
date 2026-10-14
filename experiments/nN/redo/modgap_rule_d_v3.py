"""modgap_rule_d_v3 (2026-10-06): step 3.  (a) the sets of T1[:1500] and C with no good d at the first component: per reading the class mod 8, k_d (first component where d is clear), t_d, and
the position of S's own 1/8 landing t*.  (b) the sets where rule B (d* = argmax t_d) misses but another d is good: which d is good and its relation to d*.  (c) the two tight sets of the S1 control for
(6,1): the exact t at which they fail.  Exact."""
import sys, collections
sys.path.insert(0, '.')
_src = open('modgap_rule_d_v1.py').read()
_src = _src.replace("out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("rules = {")[0])
from modgap_lib_v1 import cascade as casc8, typ8
out = open('modgap_rule_d_v3.out', 'w'); out.write(__doc__ + "\n")
def short(x): return str(x) if len(str(x)) < 14 else '%s..(%d)' % (str(x)[:8], len(str(x)))
nogood = []; bmiss = []
for name, sets in (('C', C), ('T1', T1[:1500])):
    for S in sets:
        I = [info(S, d) for d in S]
        if not any(x['good'] for x in I): nogood.append((name, S, I))
        dstar = max(I, key=lambda x: (x['t'], x['d']))
        if not dstar['good'] and any(x['good'] for x in I): bmiss.append((name, S, I, dstar))
out.write("(a) sets with no good d at the first component: %d\n" % len(nogood))
for name, S, I in nogood:
    ks = {d: kd(S, d, 40) for d in S}; t8 = casc8(S)
    out.write("  [%s] classes mod 8 in size order %s; k_d %s; t* vs t_d ordering (t* < every t_d: %s); R(d) buckets %s\n" %
              (name, ''.join(typ8(d) for d in S), [ks[d] for d in S], all(t8 < x['t'] for x in I), [('>=1' if x['R'] >= 1 else '<1') for x in I]))
out.write("\n(b) sets where rule B misses but another d is good: %d\n" % len(bmiss))
for name, S, I, dstar in bmiss:
    good = [x['d'] for x in I if x['good']]
    srt = sorted(I, key=lambda x: x['t'])
    out.write("  [%s] classes %s; d* has rank %d (class %s); good ranks %s; rank of the good d with the largest t_d among good: %d; t_d order of d*: %d of 7; R(d*) < 1: %s\n" %
              (name, ''.join(typ8(d) for d in S), S.index(dstar['d']), typ8(dstar['d']), [S.index(g) for g in good],
               S.index(max([x for x in I if x['good']], key=lambda x: x['t'])['d']), 1 + [x['d'] for x in srt].index(dstar['d']), dstar['R'] < 1))
out.write("\n(c) the two tight sets: for each d the first component of the other six at 1/7 and d's clear points in it\n")
for S in ((1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 7, 12)):
    for d in S:
        T = [x for x in S if x != d]; l, r = components(T, 1)[0]
        out.write("  S=%s d=%d: first component [%s, %s]; d clear in it: %s; k_d = %s\n" % (S, d, l, r, d_clear_in(d, l, r), kd(S, d, 40)))
out.close(); print(open('modgap_rule_d_v3.out').read()[len(__doc__):][:5500])
