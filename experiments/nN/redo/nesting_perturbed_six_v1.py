"""E389c (2026-10-05), nesting_perturbed_six_v1: E389's statement on sixes near the crossing family.
For each exact crossing member of the J=1 tree (7,567) the first six readings are perturbed (each of readings 2..6, relative
size drawn from {+-10^-3, +-10^-4, +-10^-5, +-10^-6}, 4 draws per member, seed fixed); for each perturbed six with K6 non-empty
in [1,7]: N_A = {v in (r6, 7 r6]: all K6 windows nested}; if N_A is non-empty also N_B and N_A ∩ N_B.  Counts, and every
perturbed six with N_A ∩ N_B non-empty individually.  Exact (Fractions).
"""
import sys, pickle, random
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from core import clear_set
from nesting_overlap_v1 import nest_set

def work(items):
    rng = random.Random(items[0][0]); st = [0, 0, 0, 0, 0]; miss = []
    for idx, x in items:
        if clear_set(x, F(1), F(7)):
            continue
        for _ in range(4):
            z = list(x[:6])
            for y in range(1, 6):
                z[y] = z[y] * (1 + rng.choice((-1, 1)) * F(1, 10 ** rng.randint(3, 6)))
            if sorted(z) != z or len(set(z)) < 6:
                continue
            st[0] += 1
            kA = clear_set(z, F(1), F(7))
            if not kA:
                st[1] += 1; continue
            nA = nest_set(kA, z[5], 7 * z[5])
            if not nA:
                continue
            st[2] += 1
            kB = clear_set(z, F(9), F(15))
            if not kB:
                st[3] += 1                                     # K'_6 empty: any v nests nothing to nest
            nAB = nest_set(kA + kB, z[5], 7 * z[5])
            if nAB:
                st[4] += 1; miss.append((idx, [float(a) for a in z], [(float(a), float(b)) for a, b in nAB[:2]]))
    return st, miss

if __name__ == '__main__':
    d = pickle.load(open('cell_members7_J1.pkl', 'rb'))
    items = d
    chunks = [items[i:i + 300] for i in range(0, len(items), 300)]
    with Pool(4) as pool:
        res = pool.map(work, chunks)
    s = [sum(r[0][i] for r in res) for i in range(5)]
    out = open('nesting_perturbed_six_v1.out', 'w'); out.write(__doc__ + "\n")
    out.write("perturbed sixes %d; K6 empty in [1,7]: %d; N_A non-empty: %d (of which K'_6 empty: %d); N_A ∩ N_B non-empty: %d\n" % tuple(s))
    for r in res:
        for m in r[1]:
            out.write("  MISS member %s six=%s v-intervals %s\n" % m)
    out.close(); print(open('nesting_perturbed_six_v1.out').read()[len(__doc__):][:3000])
