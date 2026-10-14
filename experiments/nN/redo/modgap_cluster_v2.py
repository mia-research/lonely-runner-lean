"""modgap_cluster_v2 (2026-10-06): the exact statements behind E413, for the 9 exceptions of modgap_nogood_v1.  Exact (integers, Fractions).
(1) S's 1/7 landing t equals the left end of the first lonely component of C = S minus d_min that lies fully inside the clear arc t in [1/(7 m), 6/(7 m)] of m = d_min  (equality of Fractions);
(2) that component lies inside the arc: its right end is at most 6/(7 m);  (3) gcd(C) = 1 (as integers: gcd of the six);  (4) the count of components of C in u = 7 m t in [0, 8] and fully inside u in [1, 6]."""
import sys, math
sys.path.insert(0, '.')
exec(open('modgap_cluster_v1.py').read().split("out = open('modgap_cluster_v1.out'")[0])
out = open('modgap_cluster_v2.out', 'w'); out.write(__doc__ + "\n")
ok1 = ok2 = ok3 = 0
for S in exc:
    m = S[0]; C = list(S[1:]); G = reduce(gcd, C)
    cs = comps(C, F(8, 7 * m))
    inside = [(l, r) for l, r in cs if 7 * m * l >= 1 and 7 * m * r <= 6]
    tt = casc7(list(S), F(1, 7 * m))
    e1 = bool(inside) and inside[0][0] == tt
    e2 = bool(inside) and inside[0][1] <= F(6, 7 * m)
    ok1 += e1; ok2 += e2; ok3 += (G == 1)
    out.write("S (%s): landing = left end of first inside component: %s; that component ends by 6/(7m): %s; gcd(C) = 1: %s; components in u in [0, 8]: %d; fully inside [1, 6]: %d\n" %
              ('%d-digit' % len(str(S[-1])) if len(str(S[-1])) > 6 else S, e1, e2, G == 1, len(cs), len(inside)))
out.write("totals over %d exceptions: equality %d, inside the arc %d, gcd 1: %d\n" % (len(exc), ok1, ok2, ok3))
out.close(); print(open('modgap_cluster_v2.out').read()[len(__doc__):])
