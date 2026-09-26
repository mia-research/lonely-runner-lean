"""Owner: measure with the cascade what empties the pool at the moment the relay stops -- per arrangement, exactly (no
frequencies as a result; counts below only tally which exact situation each arrangement is in).
Every set of 7 distinct whole-number readings in 1..24 of the slowest runner (all runners moving), cascade from the bound.
At the final hand-off (the last setter s leaves the slot at t_f and nobody is in it), for every other runner j:
  used    : j set a move earlier in this relay (it passed through the slot during the relay)
  arrival : time until j reaches the slot's entry edge, (8k - 1)/(8 d_j) - t_f, compared with s's last stretch J
  state   : 'just left' (position in [1/8, 1/8 + J d_j], i.e. it left the slot during s's last stretch),
            'far'       (otherwise)
The pool is empty when no runner's arrival falls inside [t_f - J, t_f]: recorded is WHY for each runner -- it is used and
still coming round, or it is unused and simply not near the edge -- and the nearest miss (smallest arrival / J)."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool

E8 = F(1, 8)
def nd(x):
    x = x % 1; return min(x, 1 - x)

def final(ds):
    t = F(1, 8 * ds[0]); setters = []; J = None
    while True:
        way = [i for i, d in enumerate(ds) if nd(d * t) < E8]
        if not way: break
        cand = {i: (F(floor(ds[i] * t - E8) + 1) + E8) / ds[i] for i in way}
        s = max(cand, key=lambda x: cand[x]); J = cand[s] - t; setters.append(s); t = cand[s]
    if not setters: return None
    s = setters[-1]; used = set(setters[:-1])
    info = []
    for i, d in enumerate(ds):
        if i == s: continue
        arr = ((floor(d * t + E8) + 1) - E8) / d - t          # time until next entry, from t_f
        pos = (d * t) % 1
        info.append((i, i in used, arr / J, pos))
    near = min(info, key=lambda x: x[2])
    n_used = sum(1 for x in info if x[1])
    return len(setters), s, n_used, near[1], float(near[2]), [float(x[3]) for x in info]

def chunk(first):
    c_used = Counter(); c_near_used = Counter(); c_near = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        r = final((first,) + rest)
        if r is None: continue
        mv, s, nu, near_used, near_ratio, _ = r
        c_used[(min(mv, 6), nu)] += 1
        c_near_used[near_used] += 1
        c_near[min(int(near_ratio * 4), 12)] += 1
    return c_used, c_near_used, c_near

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    cu = Counter(); cnu = Counter(); cn = Counter()
    for a, b, c in parts: cu.update(a); cnu.update(b); cn.update(c)
    tot = sum(cnu.values())
    print(f"arrangements with at least one move: {tot}")
    print(f"  (moves capped at 6, other runners already used in the relay) at the final hand-off: {sorted(cu.items())}")
    print(f"  the nearest miss is a runner already used in the relay: {cnu[True]}; an unused runner: {cnu[False]}")
    print(f"  nearest miss: its arrival in units of J (quarters; 4 = arrives exactly one J after the exit): {sorted(cn.items())}")
