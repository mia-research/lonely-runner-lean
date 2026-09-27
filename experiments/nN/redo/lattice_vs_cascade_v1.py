"""The lattice ladder against the cascade, every set of 7 distinct whole-number readings in 1..24 (the slowest runner of
the arrangement c, c + d_1, ..., c + d_7, every runner moving).  Exact.

Lattice D: instants (8j+1)/(8D) = j/D + 1/(8D), j in Z/D -- the rung j/D plus the deviation 1/(8D).  A reading d = mD
reads m/8 there, so the multiples of D form a grid read by residues mod 8 and are clear iff m mod 8 != 0 (none in the
subject's slot); the other readings are placed by the rung.  D is LIVE when no reading is = 0 mod 8D.
L0 = least live D.  D* = least D that clears (some j).  k = live lattices in [L0, D*).

Recorded per set: L0, D*, k; the cascade's landing t* = (8K+1)/(8e), its rung q = e/gcd(K,e); whether t* is a lattice
instant of L0 or of D*, i.e. D(8K+1) = e(8j+1) for some j.  For k > 0 (L0 fails) the blockers at L0 are kept for the
perturbation step (v2)."""
import itertools, sys
from fractions import Fraction as F
from math import gcd, floor
from collections import Counter
from multiprocessing import Pool

E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)

def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)

def landing(T, t):
    for e in T:
        x = e * t - E8
        if x.denominator == 1: return e, int(x)

def clear_js(T, D):
    """numerators j in [0, D) with every reading's residue d(8j+1) mod 8D in [D, 7D]"""
    out = []
    for j in range(D):
        a = 8 * j + 1
        if all(D <= (d * a) % (8 * D) <= 7 * D for d in T): out.append(j)
    return out

def live(T, D): return all(d % (8 * D) for d in T)

def study(T):
    L0 = next(D for D in itertools.count(1) if live(T, D))
    D = L0; k = 0
    while True:
        if live(T, D):
            js = clear_js(T, D)
            if js: break
            k += 1
        D += 1
    ts = cascade(T); e, K = landing(T, ts); g = gcd(K, e); q = e // g
    on = lambda DD: any(DD * (8 * K + 1) == e * (8 * j + 1) for j in range(DD))
    return dict(L0=L0, Ds=D, k=k, e=e, K=K, q=q, onL0=on(L0), onDs=on(D), e_eq_Ds=(e == D), q_eq_Ds=(q == D))

def chunk(first):
    c = Counter(); kh = Counter(); Dh = Counter(); L0h = Counter(); rel = Counter(); worst = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; r = study(T)
        c['sets'] += 1; kh[r['k']] += 1; Dh[r['Ds']] += 1; L0h[r['L0']] += 1
        c['cascade instant is a lattice instant of D*'] += r['onDs']
        c['cascade instant is a lattice instant of L0'] += r['onL0']
        c['cascade setter e == D*'] += r['e_eq_Ds']
        c['cascade rung q == D*'] += r['q_eq_Ds']
        rel[('q|D*' if r['Ds'] % r['q'] == 0 else ('D*|q' if r['q'] % r['Ds'] == 0 else 'neither'))] += 1
        if r['k'] > 0: worst.append((r['k'], T, r['L0'], r['Ds'], r['e'], r['K']))
    worst.sort(reverse=True)
    return c, kh, Dh, L0h, rel, worst[:40], [w for w in worst]

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); kh = Counter(); Dh = Counter(); L0h = Counter(); rel = Counter(); worst = []; allk = []
    for a, b, d, l, r, w, al in parts:
        c.update(a); kh.update(b); Dh.update(d); L0h.update(l); rel.update(r); worst += w; allk += al
    for k_, v in c.items(): print(f"{k_}: {v}")
    print("k (live lattices that fail before one clears):", sorted(kh.items()))
    print("L0:", sorted(L0h.items()))
    print("D*:", sorted(Dh.items()))
    print("cascade rung q against D*:", sorted(rel.items()))
    worst.sort(reverse=True)
    print("largest k (k, readings, L0, D*, cascade e, K):")
    for w in worst[:25]: print("  ", w)
    with open('lattice_vs_cascade_v1_exceptions.txt', 'w') as f:
        for w in sorted(allk, reverse=True): f.write(repr(w) + "\n")
    print("exceptions (k > 0) written:", len(allk))
