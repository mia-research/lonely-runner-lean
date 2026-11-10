# E833: soundness test of the plane-split window certifier: for each known exact carve (rho7 in [23,25)) the boxes containing it at D = 1, 2, ..., 1024 must all be uncertified by cert_poly with the tie planes.
import glob, pickle, sys
from fractions import Fraction as F
sys.argv = ['x']
exec(open('frontier_plane_cert_v1.py').read().split("def work(item):")[0])
carves = []
for f in sorted(glob.glob('frontier_box_carve_v1_23_25_s*.pkl')): carves += pickle.load(open(f, 'rb'))
for f in sorted(glob.glob('frontier_band_carve_v1_k3_s*.pkl')): carves += pickle.load(open(f, 'rb'))
for f in sorted(glob.glob('frontier_seam_anneal_v1_s*.out')):
    for l in open(f):
        if l.startswith('[') and l.count(',') == 5: carves.append([float(x) for x in l.strip('[]\n ').split(',')])
carves = [c for c in carves if 23 <= c[5] < 25]
bad = 0; tested = 0
for c in carves:
    D = 1
    while D <= 1024:
        n = tuple(int(F(v) * D) for v in c); tested += 1
        if cert_poly(corners(D, n), PLANES): bad += 1; print('CERTIFIED a box containing a carve at D =', D, n)
        D *= 2
print('carves', len(carves), '| boxes tested', tested, '| certified boxes containing a carve (soundness violations):', bad)
