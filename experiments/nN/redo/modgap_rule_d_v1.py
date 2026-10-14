"""modgap_rule_d_v1 (2026-10-06): candidate selection rules for the removed reading d.  For each residual member and each d: T_d = S minus d; t_d = the first lonely instant of T_d at 1/7; C(d) = [l_d, r_d]
its first component; good(d) = d has a clear point (>= 1/8) in C(d) (clear_in_interval_iff: clear at l, or E_d(l) <= r).  Rules (each picks one d per set, from S alone, no search over good(d)):
  A argmin_d t_d   B argmax_d t_d   C argmax_d R(d) = 4 d (r_d - l_d)   D the d with the soonest edge E_d(l_d) - l_d among those blocked at l_d (else any clear)
  E d_max   F second largest   G the d maximising the number of other readings in T_d's component width ... (omitted)   H argmax_d r_d   I argmin_d r_d   J argmax_d (r_d - l_d)
Success counts over the stored members (C, BS, DA, DB, T1[:1500]).  Exact (Fractions)."""
import sys, collections
sys.path.insert(0, '.')
_src = open('modgap_strengthen_v1.py').read()
_src = _src.replace("out = open('modgap_strengthen_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("for name, sets in (('C', C)")[0])
out = open('modgap_rule_d_v1.out', 'w'); out.write(__doc__ + "\n")
def info(S, d):
    T = [x for x in S if x != d]; l, r = components(T, 1)[0]
    good = d_clear_in(d, l, r)
    E = (F(8 * round(d * l) + 1, 8 * d) - l) if cd(d * l) < E8 else F(0)
    return dict(d=d, t=l, l=l, r=r, good=good, R=4 * d * (r - l), edge=E, w=r - l)
rules = {'A argmin t_d': lambda I: min(I, key=lambda x: (x['t'], x['d'])), 'B argmax t_d': lambda I: max(I, key=lambda x: (x['t'], x['d'])),
         'C argmax R(d)': lambda I: max(I, key=lambda x: (x['R'], x['d'])), 'D soonest edge': lambda I: min(I, key=lambda x: (x['edge'], -x['d'])),
         'E d_max': lambda I: max(I, key=lambda x: x['d']), 'F second largest': lambda I: sorted(I, key=lambda x: x['d'])[-2],
         'H argmax r_d': lambda I: max(I, key=lambda x: (x['r'], x['d'])), 'I argmin r_d': lambda I: min(I, key=lambda x: (x['r'], x['d'])),
         'J argmax width': lambda I: max(I, key=lambda x: (x['w'], x['d'])), 'K argmax (width * d)': lambda I: max(I, key=lambda x: (x['w'] * x['d'], x['d']))}
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1 [:1500]', T1[:1500])):
    c = collections.Counter(); n = 0; goodcount = collections.Counter()
    for S in sets:
        n += 1; I = [info(S, d) for d in S]
        goodcount[sum(x['good'] for x in I)] += 1
        for rn, rf in rules.items(): c[rn] += rf(I)['good']
    out.write("\n==== %s: %d sets;  number of good d per set: %s\n" % (name, n, dict(sorted(goodcount.items()))))
    for rn in rules: out.write("  rule %-24s picks a good d in %d of %d\n" % (rn, c[rn], n))
out.close(); print(open('modgap_rule_d_v1.out').read()[len(__doc__):])
