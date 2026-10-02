# Move 1 of the cascade on the AP with k deformed runners: is the carried blocker the reading pinned on the entering edge (p0 = 7 exactly)?
import sys, random
sys.argv = [sys.argv[0]]
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
for k in (1, 2, 3, 4):
    rnd = random.Random(310 + k); base = [F(x) for x in range(1, 8)]
    tot = pin7 = other = 0; others = Counter(); setter_first = Counter()
    for r in range(30):
        movers = tuple(sorted(rnd.sample(range(7), k))); target = list(base)
        for m in movers: target[m] = max(F(3, 10), base[m] + F(rnd.randint(-150, 250), 100))
        for st in range(31):
            s = F(st, 30); rhos = [base[i] + ((target[i] - base[i]) * s if i in movers else 0) for i in range(7)]
            steps, _ = path(rhos)
            if not steps: continue
            mv = steps[0]
            for i, how, p0, sh in mv["new"]:
                if how != "carried": continue
                tot += 1
                if p0 == 7: pin7 += 1
                else: other += 1; others[round(float(p0), 1)] += 1
    print("k=%d: move-1 carried blockers %d; pinned on the entering edge (p0 = 7 exactly) %d; others %d; p0 of the others (rounded): %s" % (k, tot, pin7, other, sorted(others.items())[:12]))
