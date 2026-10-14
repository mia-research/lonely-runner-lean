"""modgap_strengthen_v3 (2026-10-06): the width of the first component C(d) = [l, r] of the six readings S minus d at 1/7, against the blocked window of d, length 1/(4d).
R(d) = 4 d (r - l).  [P] if R(d) >= 1 then d is clear somewhere in C(d) (a closed interval of length at least the open window's length cannot lie inside one blocked window; blocked windows are
disjoint open intervals of length 1/(4d), so a closed interval of that length or more meets a clear point).  Recorded per member population: for d = d_max, and for the best d, the counts of R >= 1 (the
interval argument settles it) and R < 1 (nested in a window or not, then settled by the exact test of v1), and the distribution of floor(R) on a log scale.  Exact (Fractions); decimals only to display."""
import sys, collections
sys.path.insert(0, '.')
_src = open('modgap_strengthen_v1.py').read()
_src = _src.replace("out = open('modgap_strengthen_v1.out', 'w'); out.write(__doc__ + \"\\n\")", "")
exec(_src.split("for name, sets in (('C', C)")[0])
out = open('modgap_strengthen_v3.out', 'w'); out.write(__doc__ + "\n")
def R(S, d):
    T = [x for x in S if x != d]
    l, r = components(T, 1)[0]
    return 4 * d * (r - l), (l, r)
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1 [:1500]', T1[:1500])):
    cmax = collections.Counter(); cbest = collections.Counter(); n = 0; interval_settles_dmax = interval_settles_any = 0; clear_but_R_lt_1 = 0
    for S in sets:
        n += 1
        Rs = {d: R(S, d)[0] for d in S}
        bucket = lambda x: ('>=1' if x >= 1 else ('[1/10,1)' if x >= F(1, 10) else ('[1/100,1/10)' if x >= F(1, 100) else '<1/100')))
        cmax[bucket(Rs[S[-1]])] += 1; cbest[bucket(max(Rs.values()))] += 1
        interval_settles_dmax += Rs[S[-1]] >= 1; interval_settles_any += any(v >= 1 for v in Rs.values())
        clear_but_R_lt_1 += sum(1 for d in S if Rs[d] < 1 and kd(S, d, 1) == 1)
    out.write("\n==== %s: %d sets\n  d = d_max: R = 4 d (r - l) buckets: %s; interval argument settles d_max in %d sets\n  best d: R buckets: %s; the interval argument settles some d in %d sets\n  pairs (set, d) with R < 1 yet d clear in the first component: %d\n" %
              (name, n, dict(cmax), interval_settles_dmax, dict(cbest), interval_settles_any, clear_but_R_lt_1))
out.close(); print(open('modgap_strengthen_v3.out').read()[len(__doc__):])
