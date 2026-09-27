"""E153: fine-shape climb maximising the number of a slow runner's blocks A.([1,7] u [9,15] u ...) that a six-reading
group (least = 1) needs from its worst start A in [1, 12].  Denominator 2520; 16 climbs from random and extremal starts.
Protections: progress file six_blocks_climb_v1.progress (each climb's result as it finishes; any shape needing more than
2 blocks flagged NEEDS>2 immediately); the six_blocks_v2 positive control must pass first."""
import random, sys
from fractions import Fraction as F
from multiprocessing import Pool
from six_blocks_v2 import worst, control
PROG = 'six_blocks_climb_v1.progress'
def climb(seed):
    rng = random.Random(1000 + seed); D = 2520
    starts = [(1.0, 1.3746, 1.7628, 2.2539, 2.5123, 3.23), (1.0, 1.3637, 1.7229, 2.2072, 2.4565, 3.1583),
              (1.0, 1.2781, 1.5849, 1.7644, 2.2574, 2.8117), (1.0, 1.2653, 1.4334, 1.5874, 1.7831, 2.2627)]
    if seed < 4: g = [int(round(x * D)) for x in starts[seed]]
    else: g = sorted({D} | {rng.randrange(D + 1, rng.choice((3, 7, 15)) * D) for _ in range(5)})
    while len(g) < 6: g = sorted(set(g + [rng.randrange(D + 1, 4 * D)]))
    best, A = worst(g)
    for step in range(250):
        h = list(g); i = rng.randrange(1, 6); h[i] += rng.choice((-1, 1)) * rng.randrange(1, D // 6)
        h = sorted(h)
        if len(set(h)) < 6 or h[0] != D or h[1] <= D: continue
        n, a = worst(h)
        if n >= best:
            g, best, A = h, n, a
            if n > 2:
                with open(PROG, 'a') as f: f.write("NEEDS>2 seed %d step %d: %s A=%s blocks %d\n" % (seed, step, [round(x / D, 4) for x in g], A, n))
    with open(PROG, 'a') as f: f.write("climb %d done: blocks %d at %s A=%s\n" % (seed, best, [round(x / D, 4) for x in g], A))
    return best, [round(x / D, 4) for x in g], str(A)
if __name__ == '__main__':
    c, shape, R = control()
    with open(PROG, 'a') as f: f.write("positive control: %s blocks (expected 2)\n" % c)
    if c != 2: print("CONTROL FAILED"); sys.exit(1)
    with Pool(8) as p: res = sorted(p.imap_unordered(climb, range(16)), key=lambda x: -x[0])
    for r in res[:8]: print("blocks needed %d at %s, worst start A = %s" % r)
    with open(PROG, 'a') as f: f.write("ALLDONE\n")
