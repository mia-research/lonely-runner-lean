"""Exact independent check of Claude's three-window report; no sampling.

Intersect closed bands directly so singleton intersections are retained.
R is eighth-time, with minimum disparity 1.
"""
from fractions import Fraction as F

core = [F(1), F(73, 25), F(99, 25), F(253, 50), F(321, 50), F(697, 100)]
V = F(363, 50)
windows = [(F(1), F(7))]
for d in core:
    bands = [(F(8*q+1)/d, F(8*q+7)/d) for q in range(int(7*d/8)+1)]
    windows = sorted(set((max(l, a), min(u, b)) for l, u in windows
                         for a, b in bands if max(l, a) <= min(u, b)))

assert windows == [(F(1), F(700, 697)), (F(425, 99), F(3100, 697)),
                   (F(150, 23), F(4700, 697))]
for l, u in windows:
    K = (V*l+1)//8
    e = F(8*K+1)/V
    assert 8*K-1 < V*l <= V*u < 8*K+1
    assert e > u and V*(u-l) < 2
    assert 0 <= K < l/(4*(u-l))+F(1, 8)
    for d in core:
        q = (d*l)//8
        assert 8*q+1 <= d*l <= d*u <= 8*q+7
    print(f'window=[{l},{u}] K={K} captured_at_L=True '
          f'exit={e} deficit={e-u} scaled_width={V*(u-l)}')
assert all(1 <= (9*d) % 8 <= 7 for d in core+[V])
print('All three core windows entirely captured; all seven readings clear at R=9.')
