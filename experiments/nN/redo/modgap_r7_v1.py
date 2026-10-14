"""modgap_r7_v1 (2026-10-06): the 1/7 interval criterion.  [L] no_long_interval_of_no_lonely_seven / exists_clear_in_interval at n = 7: if S minus d has a lonely component [l, r] at 1/7 of length
at least 2/(7 d), then S has a lonely instant at 1/7.  So R7(d) = (7 d / 2)(r - l) >= 1 for the first component of S minus d settles 1/7-loneliness of S with no further work.  Per population: the
number of sets with some d, R7(d) >= 1 at the first component; at any of the first 5 components; and d = d_max alone.  Populations: 28 hard, hard 41-60, the stored members, and S1 = {1} + 6-subsets of [2,24] first 20,000
(control, includes the no-1/7 sets).  Exact."""
import sys, re, json, collections, itertools, math
sys.path.insert(0, '.')
_src = open('modgap_f7_forced_v1.py').read()
_src = _src.split("out = open('modgap_f7_forced_v1.out'")[0]
exec(_src)
def casc7b(T, t):
    return casc7(T, t)
def comps(T, k):
    t = casc7(T, F(1, 7 * min(T))); out = []
    for _ in range(k):
        best = None
        for x in T:
            N = math.ceil(x * t - F(6, 7)); e = (N + F(6, 7)) / x
            if best is None or e < best[0]: best = (e, [x])
            elif e == best[0]: best[1].append(x)
        r, cl = best; out.append((t, r))
        Fs = [F(7 * (math.floor(x * r - F(6, 7)) + 1) + 1, 7 * x) for x in cl]
        t = casc7(T, max(Fs))
    return out
out = open('modgap_r7_v1.out', 'w'); out.write(__doc__ + "\n")
def s1():
    n = 0
    for r in itertools.combinations(range(2, 25), 6):
        yield (1,) + r; n += 1
        if n >= 20000: return
tight = [(1, 2, 3, 4, 5, 6, 7), (1, 2, 3, 4, 5, 7, 12), (1, 2, 3, 4, 5, 6, 14), (1, 2, 3, 4, 5, 6, 21), (1, 2, 3, 4, 5, 6, 28)]
for name, sets in (('28 hard', hard), ('hard 41-60', h2), ('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1[:1500]', T1[:1500]), ('S1 control', s1()), ('no-1/7 sets (AP6 family and tight)', tight)):
    c = collections.Counter(); n = 0
    for S in sets:
        n += 1
        any1 = anyk = dmax1 = False
        for d in S:
            T = [x for x in S if x != d]
            cs = comps(T, 5)
            R = [F(7 * d, 2) * (r - l) for l, r in cs]
            any1 |= R[0] >= 1; anyk |= any(x >= 1 for x in R)
            if d == S[-1]: dmax1 = R[0] >= 1
        c['some d: R7 >= 1 at the first component'] += any1
        c['some d: R7 >= 1 at one of the first 5 components'] += anyk
        c['d = d_max: R7 >= 1 at the first component'] += dmax1
    out.write("\n==== %s: %d sets\n" % (name, n))
    for k, v in sorted(c.items()): out.write("  %s: %d\n" % (k, v))
out.close(); print(open('modgap_r7_v1.out').read()[len(__doc__):])
