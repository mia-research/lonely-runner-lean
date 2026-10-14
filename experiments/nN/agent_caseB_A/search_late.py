"""Search for late shapes (not lonely anywhere in [1,7]) from many random starts by
exact descent on the measure of the lonely set inside [1,7].  Exact Fractions only.
Writes late_found.txt and progress_search.txt."""
import random, sys, time
from fractions import Fraction as F
from core import *
D = 2520

def meas17(ns):
    n0 = ns[0]
    cur = [(F(1), F(7))]
    for nd in ns[1:]:
        s = F(nd, n0); new = []
        for a, b in cur:
            k = 0
            while True:
                wl, wr = F(8*k+1)/s, F(8*k+7)/s
                if wl > b: break
                L, Rr = max(a, wl), min(b, wr)
                if L <= Rr: new.append((L, Rr))
                k += 1
        cur = new
        if not cur: return F(0), 0
    return sum(b - a for a, b in cur), len(cur)

def run(nstarts, seed):
    rng = random.Random(seed)
    found = []
    t0 = time.time()
    for st in range(nstarts):
        n6 = rng.randint(7*D+1, 9*D)
        cur = (D, *sorted(rng.sample(range(D+1, n6), 5)), n6)
        m, c = meas17(cur)
        step = 200
        for it in range(3000):
            if c == 0: break
            nxt = list(cur)
            for _ in range(rng.randint(1, 2)):
                i = rng.randint(1, 6); nxt[i] += rng.randint(-step, step)
            nxt = tuple(nxt)
            if not is_band(nxt): continue
            m2, c2 = meas17(nxt)
            if c2 == 0 or m2 <= m:
                cur, m, c = nxt, m2, c2
            if it % 500 == 499: step = max(10, step // 2)
        if c == 0:
            found.append(cur)
        with open('progress_search.txt', 'w') as f:
            f.write(f"start {st+1}/{nstarts} found {len(found)} elapsed {time.time()-t0:.0f}s\n")
    return found

if __name__ == '__main__':
    n = int(sys.argv[1]); seed = int(sys.argv[2])
    # positive control: a known late shape must have measure 0 on [1,7]
    ctrl = (2520, 5900, 8138, 10561, 13139, 14587, 18719)
    assert meas17(ctrl)[1] == 0 and landing(ctrl)[0] >= 9, "positive control failed"
    assert meas17((2520, 2*2520, 3*2520, 4*2520, 5*2520, 6*2520, 8*2520))[1] > 0
    found = run(n, seed)
    with open(f'late_found_{seed}.txt', 'w') as f:
        for ns in found: f.write(' '.join(map(str, ns)) + '\n')
    print("found", len(found))
