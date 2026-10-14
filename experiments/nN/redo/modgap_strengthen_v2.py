"""modgap_strengthen_v2 (2026-10-06): which reading d can be removed.  For each residual member, the set D1 = {d : k_d = 1} (the first component of the other six at 1/7 contains a point clear for d at 1/8).
Recorded: |D1|; the rank of d in D1 (0 = smallest reading); the class of d mod 8 (m multiple of 8, o odd, t 2 mod 4, f 4 mod 8); whether d is in the setters P of S's own cascade at 1/8, whether d is S's opener
or closer at its landing; and the candidate rules: R_a 'every member has d_max in D1', R_b 'the opener of S's landing is in D1', R_c 'a multiple of 8 is in D1', R_d 'the second largest is in D1',
R_e 'the closer is in D1'.  Exact.  Functions from modgap_strengthen_v1."""
import sys, collections
sys.path.insert(0, '.')
_src = open('modgap_strengthen_v1.py').read()
_src = _src.replace("out = open('modgap_strengthen_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("for name, sets in (('C', C)")[0])
from modgap_lib_v1 import cascade_path, openers, component, typ8
out = open('modgap_strengthen_v2.out', 'w'); out.write(__doc__ + "\n")
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1 [:1500]', T1[:1500])):
    c = collections.Counter(); rank = collections.Counter(); cls = collections.Counter(); n = 0
    for S in sets:
        n += 1
        D1 = [d for d in S if kd(S, d, 3) == 1]
        path = cascade_path(S); P = {x for _, x in path if x}; t = path[-1][0]
        op = openers(S, t); tR, cl = component(S, t)
        c[('|D1|', len(D1))] += 1
        for d in D1:
            rank[S.index(d)] += 1; cls[typ8(d)] += 1
        c['R_a d_max in D1'] += S[-1] in D1
        c['R_b opener in D1'] += op[0] in D1
        c['R_e closer in D1'] += cl[0] in D1
        c['R_c some multiple of 8 in D1'] += any(d % 8 == 0 for d in D1)
        c['R_d second largest in D1'] += S[-2] in D1
        c['R_f some setter in D1'] += any(d in P for d in D1)
        c['R_g all of D1 are setters'] += all(d in P for d in D1)
        c['R_h D1 empty'] += not D1
    out.write("\n==== %s: %d sets\n" % (name, n))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    out.write("  rank in S of d in D1: %s\n  class mod 8 of d in D1: %s\n" % (dict(sorted(rank.items())), dict(sorted(cls.items()))))
out.close(); print(open('modgap_strengthen_v2.out').read()[len(__doc__):])
