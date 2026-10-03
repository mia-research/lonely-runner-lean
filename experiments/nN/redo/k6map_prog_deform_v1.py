# K6 of deformations of the progression 1..6 and of 1,2,3,4,5,7: exact window structure (components, point windows, longest) as one reading moves along a rational grid,
# and under joint exact perturbations.  Shows which windows survive deformation (open windows) and which are point windows that appear/disappear.
import random
from collections import Counter
from k6map_lib_v1 import *
def desc(rho):
    W = K6(rho); return len(W), sum(1 for a, b in W if a == b), max(b - a for a, b in W)
base = [F(i) for i in range(1, 7)]
print("progression 1..6:", [(str(a), str(b)) for a, b in K6(base)])
# one-reading deformations of reading k (2..6) by delta in a grid of 1/200, delta in [-0.45, 0.45]; windows count / points
for k in range(1, 6):
    cnt = Counter(); Ls = []
    for d in range(-90, 91):
        if d == 0: continue
        rho = list(base); rho[k] = base[k] + F(d, 200)
        if not all(a < b for a, b in zip(rho, rho[1:])): continue
        n, p, L = desc(rho); cnt[(n, p)] += 1; Ls.append(L)
    print("reading %d moved by d/200, |d|<=90: (components, point windows) -> number of deformations:" % (k + 1), sorted(cnt.items()), "| longest component range [%s, %s]" % (min(Ls), max(Ls)))
# joint exact perturbations
rnd = random.Random(2); cnt = Counter(); Ls = []
for _ in range(3000):
    rho = [F(1)] + [base[k] + F(rnd.randint(-100, 100), 1000) for k in range(1, 6)]
    if not all(a < b for a, b in zip(rho, rho[1:])): continue
    n, p, L = desc(rho); cnt[(n, p)] += 1; Ls.append(L)
print("joint perturbations |d|<=0.1 (3000 draws): (components, point windows) -> count:", sorted(cnt.items()), "| longest component range [%s, %s] = [%.5f, %.5f]" % (min(Ls), max(Ls), float(min(Ls)), float(max(Ls))))
base2 = [F(x) for x in (1, 2, 3, 4, 5, 7)]
print("1,2,3,4,5,7:", [(str(a), str(b)) for a, b in K6(base2)])
