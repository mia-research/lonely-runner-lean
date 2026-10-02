# Over EVERY run and step of multi_mover_map_v1 (same seeds): steps with no lonely R in (0, 9.5], and the deepest skip.
import sys, random
sys.argv = [sys.argv[0]]
exec(open('multi_mover_map_v1.py').read().split('\nif __name__ ==')[0])
for k in (3, 4):
    rnd = random.Random(309 + k); empty = 0; steps = 0; deepest = 0; ex = None
    bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]),
             ("g14", [F(x) for x in (1, 2, 3, 4, 5, 7, 14)]), ("3AP", [F(3 * x) for x in range(1, 8)])]
    for name, base in bases:
        runs = 40 if name == "AP" else 13
        for r in range(runs):
            movers = tuple(sorted(rnd.sample(range(7), k))); target = list(base)
            for m in movers:
                span = base[m] if base[m] < 6 else F(6)
                target[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-110, 110), 100) * span / 4)
            Lf, seq = run(base, movers, target)
            for s, ci, sk in seq:
                steps += 1
                if ci is None: empty += 1
                elif len(sk) > deepest: deepest = len(sk); ex = (name, movers, float(s), ci)
    print("k=%d: steps %d, steps with no lonely R in (0,9.5]: %d, deepest skip (frozen components blocked before the landing): %d at %s" % (k, steps, empty, deepest, ex))
