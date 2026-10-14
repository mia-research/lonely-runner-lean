"""modgap_family_v4 (2026-10-06): the members of modgap_family_v3 in which one odd reading sets the instant twice.  For each: the setter sequence, the size of that odd reading in digits,
the jump lengths between its two settings as d * (t_j - t_i) (R1: a reading in the way twice crossed the clear arc, d (t_j - t_i) >= 3/4), and the ratio of that odd reading to d_max.  Exact."""
import sys, collections, random
sys.path.insert(0, '.')
exec(open('modgap_family_v2.py').read().split("out = open('modgap_family_v2.out'")[0])
out = open('modgap_family_v4.out', 'w'); out.write(__doc__ + "\n")
n = 0
for K in (18, 27):
    rnd = random.Random(20261006 + K); mem = []; tried = 0
    while tried < 60000 and len(mem) < 1500:
        tried += 1
        S = build(rnd, K, 1)
        if S is not None and full_residual(S): mem.append(S)
    for S in dict.fromkeys(mem):
        path = cascade_path(S); ts = [p for p, _ in path]; seq = [d for _, d in path[1:]]
        c = collections.Counter(seq)
        for d, v in c.items():
            if d % 8 and v >= 2:
                idx = [i + 1 for i, x in enumerate(seq) if x == d]
                gaps = [float(d * (ts[idx[k + 1]] - ts[idx[k]])) for k in range(len(idx) - 1)]
                n += 1
                out.write("K=%d  odd reading of %d digits (d_max has %d digits; d/d_max ~ 10^%d) sets %d times; setter role string %s; d*(t_j - t_i) between settings (display) %s\n" %
                          (K, len(str(d)), len(str(S[-1])), len(str(d)) - len(str(S[-1])), v, ''.join('M' if x % 8 == 0 else 'O' for x in seq), ["%.3g" % g for g in gaps]))
out.write("\ncases: %d\n" % n); out.close(); print(open('modgap_family_v4.out').read()[len(__doc__):][:3500])
