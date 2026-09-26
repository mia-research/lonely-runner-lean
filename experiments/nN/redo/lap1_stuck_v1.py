"""The 232 sets of E102b (lap1_reopen_v1) where no single move of one reading by +-1, +-2 brings the cascade back to a
lap <= 1 opening: list them with the cascade's landing (e, K, R*) and, at every lap-0/1 opening at or after the bound,
the runners in the slot.  Exact (Fraction), BSM."""
import itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from cascade_vs_menu_v1 import views
from lap1_reopen_v1 import cascade, landing, E8

def stuck(T):
    for j, d in enumerate(T):
        for dl in (-2, -1, 1, 2):
            nd_ = d + dl
            if nd_ <= 0 or nd_ in T: continue
            U = tuple(sorted(T[:j] + (nd_,) + T[j + 1:]))
            if landing(U, cascade(U))[1] <= 1: return False
    return True

def chunk(first):
    out = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; ts = cascade(T)
        if any(t == ts for t in views(T).values()): continue
        if stuck(T): out.append(T)
    return out

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    S = [T for p in parts for T in p]
    print(f"stuck sets: {len(S)}")
    print("d_min:", sorted(Counter(T[0] for T in S).items()))
    print("spread S = d_max/d_min:", sorted(Counter(str(F(T[-1], T[0])) for T in S).items(), key=lambda x: F(x[0]))[:40])
    for T in S[:25]:
        ts = cascade(T); e, K = landing(T, ts); m = T[0]
        b0 = F(1, 8 * m)
        cands = sorted({(F(8 * k + 1, 8 * x), x, k) for x in T for k in (0, 1) if F(8 * k + 1, 8 * x) >= b0})
        row = '; '.join(f"{x}@{k}:{[d for d in T if nd(d * t) < E8]}" for t, x, k in cands)
        print(f"{T} t*={ts} e={e} K={K} R*={8 * m * ts}  | {row}")
