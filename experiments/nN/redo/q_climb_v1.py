"""Push Q(F)'s worst ratio e/max(s, T0) (q_window_v1) as high as it goes, exactly, by one-reading integer moves of a
six-set (readings positive, distinct; accepted when the ratio does not fall).  Starts: the 60 worst sets of
q_window_v1's sample plus 60 random, each scaled by 8 for room.  Report the largest ratios and their sets."""
import random, sys, re
from fractions import Fraction as F
from multiprocessing import Pool
from q_window_v1 import worst_ratio

def climb(args):
    Fs, seed, iters = args
    rnd = random.Random(seed); cur = worst_ratio(Fs)[0]
    for _ in range(iters):
        i = rnd.randrange(6); step = max(1, Fs[i] // rnd.choice((4, 16, 64)))
        G = list(Fs); G[i] += rnd.choice((-1, 1)) * rnd.randint(1, step)
        G = sorted(G)
        if G[0] < 1 or len(set(G)) < 6 or G[-1] > 4000: continue
        r = worst_ratio(G)[0]
        if r >= cur: Fs, cur = G, r
    b, arg, T0 = worst_ratio(Fs)
    return Fs, b, arg, T0

if __name__ == '__main__':
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    starts = []
    for line in open('q_window_v1.out'):
        m = re.search(r'F (\[[^\]]*\])', line)
        if m: starts.append([8 * x for x in eval(m.group(1))])
    rnd = random.Random(5)
    while len(starts) < 120: starts.append(sorted(rnd.sample(range(8, 800), 6)))
    with Pool() as pool: res = pool.map(climb, [(S, 100 + i, iters) for i, S in enumerate(starts)])
    res.sort(key=lambda r: -r[1])
    print(f"climbs {len(res)} ({iters} proposals); Q fails (ratio > 7): {sum(r[1] > 7 for r in res)}; max ratio {float(res[0][1]):.4f}")
    for Fs, b, arg, T0 in res[:12]:
        m = min(Fs)
        print(f"  ratio {float(b):.4f}  F/min {[round(x / m, 4) for x in Fs]}  stretch R_F [{float(8*m*arg[0]):.3f}, {float(8*m*arg[1]):.3f}]  T0 R_F {float(8*m*T0):.3f}  F {Fs}")
