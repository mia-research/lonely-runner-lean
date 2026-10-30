"""E663 diagnosis: for the cells where |Delta - Delta_lim| > 4G, which component of K(r) Delta_lim picked
(degenerate a = b or not) and where the cascade landed relative to K(r)'s components. Exact Fractions."""
import math
from fractions import Fraction as F
from collections import Counter
src = open('two_block_cells_v1.py').read().split('fams = [')[0]
ns = {}; exec(compile(src, 'm', 'exec'), ns); K, dlim, shift = ns['K'], ns['dlim'], ns['shift']
tab = Counter(); ex = []
for p, b in [(2, F(3, 2)), (6, F(2, 3)), (3, F(7, 4)), (5, F(4, 3))]:
    Q = b.denominator
    for r in range(Q):
        comps = K(p, b, r, F(0), F(8))
        taus = [F(j, 48) for j in range(48)] + [F(1, 97), F(13, 101), F(29, 103), F(1, 2) + F(1, 1009), F(61, 89), F(5, 7) + F(1, 997), F(96, 97)]
        for tau0 in taus:
            N = 4000 * Q + r; G = 1 / (8 * (N + tau0)); d, _ = shift(p, b, N, tau0, False)
            dl = dlim(comps, tau0)
            if abs(d - dl) <= 4 * G: continue
            picked = next((a, c) for a, c in comps if tau0 <= c)
            T = tau0 + d
            land = next(((a, c) for a, c in comps if a - F(1, 10**6) <= T <= c + F(1, 10**6)), None)
            key = (('picked degenerate' if picked[0] == picked[1] else 'picked interval'),
                   ('landing earlier' if d < dl else 'landing later'),
                   ('landing near a component of K' if land else 'landing not near K'))
            tab[key] += 1
            if len(ex) < 6: ex.append((p, str(b), r, str(tau0), 'picked', tuple(map(str, picked)), 'landing T', str(T), float(T)))
for kk, vv in sorted(tab.items(), key=lambda x: -x[1]): print(vv, kk)
for e in ex: print("  ", e)
