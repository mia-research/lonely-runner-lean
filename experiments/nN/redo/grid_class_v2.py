"""E128: grid references at every natural scale.  Reference scale lam = s_j / m (reading j exactly on grid point m,
m = 1..M); grid n_i = floor or ceil of s_i / lam; class c odd with R = c / lam in [1,7] u [9,15]; reading i on lap
floor(c n_i / 8), a captured reading (c n_i = 0 mod 8) on the lap before or at.  Pairwise compatibility decides (with
relocation).  Reports the least m that works.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
def compat(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def grid_class(s, M=12):
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m
            options = [sorted({floor(x / lam), ceil(x / lam)}) for x in s]
            for c in range(1, 200, 2):
                R = c / lam
                if R > 15: break
                if R < 1 or 7 < R < 9: continue
                for n in itertools.product(*options):
                    if min(n) < 1: continue
                    base = [(c * q) // 8 for q in n]
                    amb = [i for i, q in enumerate(n) if (c * q) % 8 == 0]
                    for adj in itertools.product(*[(-1, 0) if i in amb else (0,) for i in range(7)]):
                        k = [b + a for b, a in zip(base, adj)]
                        if min(k) >= 0 and compat(s, k): return m
    return None
def _study():
  c = Counter(); D1 = 27720; rnd = random.Random(41)
  for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
      T = [int(round(x * D1)) for x in sd]
      for step in range(1500):
          L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-500, 501)
          U = sorted(set(L))
          if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
          s = [F(d, D1) for d in U]
          if clear_set(s, F(1), F(7)): continue
          T = U
          if step % 10 == 0: c[grid_class(s)] += 1
  print("late band shapes: least m with a grid reference s_j/m and a class that works:", sorted(c.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))

if __name__ == "__main__": _study()
