"""E649 test of the half-step instant. Records: gap strip (G > 0) with N = own block (the E647 population with the
nearest reading at the own step). The other block, seen from the subject, is the AP x + j s (j < q), x its nearest
reading, s its step. Instant: t_n = (2n+1)/(2s) in W = [1/(8u), 7/(8Ju)]; at t_n the other block has two phases,
x t_n and x t_n + 1/2. Named instant checked by exact loneliness of the whole set at t_n (not against the landing).
Records with some certified t_n are counted, misses tabulated by p and b; exact Fractions."""
import pickle, math
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
cert = Counter(); tot = Counter(); bad = 0; seen = set()
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0: continue
    A = G + (p - 1); v = sp(p, A, b)
    ownb = list(range(p)) if k < p else list(range(p, 8)); oth = [i for i in range(8) if i not in ownb]
    u = F(1) if k < p else b; s = b if k < p else F(1)
    ds = [abs(v[i] - v[k]) for i in range(8) if i != k]
    if min(ds) < u: continue
    J = max(ownb.index(k), len(ownb) - 1 - ownb.index(k))
    lo, hi = F(1, 8) / u, F(7, 8) / (J * u)
    x = min(abs(v[i] - v[k]) for i in oth)
    ok = False
    n = max(0, math.floor(lo * s - F(1, 2)))
    while True:
        tn = F(2 * n + 1, 2) / s
        if tn > hi: break
        if tn >= lo:
            ph = (x * tn) % 1
            if (E <= ph <= 3 * E) or (5 * E <= ph <= 7 * E):
                if not all(dist(d * tn) >= E for d in ds): bad += 1
                ok = True; break
        n += 1
    key = (p, 'own block size %d' % len(ownb), 'b<1' if b < 1 else 'b>1')
    tot[key] += 1; cert[key] += ok
print("certificate failures (named instant not lonely):", bad)
for kk in sorted(tot): print("%7d of %7d certified  %s" % (cert[kk], tot[kk], kk))
print("total: %d of %d" % (sum(cert.values()), sum(tot.values())))
