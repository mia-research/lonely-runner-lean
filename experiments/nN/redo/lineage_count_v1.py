"""Where along each deformation path is the number of lonely stretches (R in [1,15]) smallest?  Grid 300 (lineage_v1's
resolution check: grid 3000 gives the same counts to within 1%).  Exact."""
from fractions import Fraction as F
from multiprocessing import Pool
from lineage_v1 import stretches
from pinchoff_v1 import targets, readings_at
def prof(args):
    name, V = args; N = 300
    D1 = [F(v - V[0]) for v in V[1:]]; W = D1[-1]; D0 = [W * j / 7 for j in range(1, 8)]
    c = [len(stretches(readings_at(D0, D1, F(i, N)))) for i in range(1, N + 1)]
    m = min(c); where = [i for i, x in enumerate(c, 1) if x == m]
    below_start = sum(1 for x in c if x < c[0])
    return name, V, c[0], m, where[0], where[-1], below_start, c[-1]
if __name__ == '__main__':
    T = [t for t in targets() if t[0].startswith('random') or 'W30' in t[0]]
    with Pool() as pool: res = pool.map(prof, T)
    from collections import Counter
    print("count just after the progression (s = 1/300):", Counter(r[2] for r in res))
    print("minimum count along the path:", Counter(r[3] for r in res))
    print("paths whose count ever drops below its starting value:", sum(1 for r in res if r[6] > 0), "of", len(res))
    for r in res:
        if r[3] < r[2] or r[3] < 4:
            print(f"  {r[0]:24s} V {r[1]}: start {r[2]}, min {r[3]} at s in [{r[4]}/300, {r[5]}/300], grid points below start {r[6]}, end {r[7]}")
    print("count at the target (s = 1):", sorted(Counter(r[7] for r in res).items()))
