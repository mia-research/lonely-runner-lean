"""n=5: moment-iteration chains for differences 1 = a <= b <= c <= d, threshold 1/5.
(1) random + grid + near-AP maps of setter patterns (ranks) and lap sequences;
(2) annealing for longest chain and largest nearest-runner reading;
(3) check of the product form of the return condition: a runner whose last opening in the chain was at lap P and which
    is in the way m moves later satisfies prod_j (5Q_j+1)/(5Q_j-1) > (5P+4)/(5P+1) over the intervening setters' laps."""
from fractions import Fraction as F
import math, random, collections
n = 5; th = F(1, n)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    t = th / ds[0]; steps = []; its = []
    while True:
        best = t; who = None; inw = set()
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                inw.add(i); k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        its.append((t, inw))
        if who is None: return steps, its
        steps.append(who); t = best
        if len(steps) > 200: return None, its
names = 'abcd'
pat = collections.Counter(); ex = {}; maxlen = 0; maxread = F(0); prodfail = 0; prodtested = 0; near_inway = 0
def rec(r):
    global maxlen, maxread, prodfail, prodtested, near_inway
    ds = [F(1)] + sorted(r)
    s, its = chain(ds)
    if s is None: print('NO STOP', r); return 0, 0
    key = ''.join(names[i] for i, _ in s)
    pat[key] += 1; ex.setdefault(key, ([str(x) for x in ds], [(names[i], k) for i, k in s]))
    maxlen = max(maxlen, len(s)); rd = n * its[-1][0]; maxread = max(maxread, rd)
    if any(0 in w for _, w in its): near_inway += 1
    # product check: for each runner, last opening index and lap
    last = {0: (0, 0)}  # nearest: opening at iterate 0, lap 0
    for j, (i, k) in enumerate(s):
        # iterate j+1 is runner i's opening at lap k; check everyone in the way at iterate j (except new setter semantics)
        for x, (jj, P) in list(last.items()):
            if x in its[j][1] and jj < j:
                prodtested += 1
                prod = F(1)
                for (_, Q) in s[jj:j]:
                    prod *= F(n * Q + 1, n * Q - 1)
                if not prod > F(n * P + n - 1, n * P + 1): prodfail += 1
        last[i] = (j + 1, k)
    return len(s), rd
random.seed(5)
step = F(1, 6)
for i in range(0, 6 * 12 + 1):
    for j in range(i, 6 * 12 + 1, 2):
        for k in range(j, 6 * 12 + 1, 3):
            rec((1 + i * step, 1 + j * step, 1 + k * step))
for _ in range(60000):
    b = 1 + F(random.randint(0, 10**5), random.choice([97, 1009, 9973]))
    c = b + F(random.randint(0, 10**5), random.choice([101, 1013, 9967]))
    d = c + F(random.randint(0, 10**5), random.choice([103, 1019, 9949]))
    rec((b, c, d))
# annealing for long chains / large nearest reading
def anneal(score_idx, seed):
    rng = random.Random(seed)
    cur = [1 + F(rng.randint(0, 4000), 400) for _ in range(3)]
    cs = rec(cur)[score_idx]; best = (cs, list(cur))
    for it in range(4000):
        T = 1.0 * (1 - it / 4000) + 0.01
        new = [max(F(1), x + F(rng.randint(-40, 40), 400 * rng.choice([1, 10, 100]))) for x in cur]
        ns = rec(new)[score_idx]
        if ns >= cs or rng.random() < math.exp((float(ns) - float(cs)) / T):
            cur, cs = new, ns
            if cs > best[0]: best = (cs, list(cur))
    return best
for sidx, label in ((0, 'chain length'), (1, 'nearest reading')):
    bests = [anneal(sidx, s) for s in range(12)]
    b = max(bests, key=lambda x: x[0])
    print(f'anneal max {label}: {float(b[0]):.4f} at ratios {[str(x) for x in sorted(b[1])]}')
print('max chain length', maxlen, '| max nearest reading', float(maxread), '| nearest in the way at an iterate:', near_inway)
print('product return condition tested', prodtested, 'violations', prodfail)
print('distinct setter patterns', len(pat))
for key, c in sorted(pat.items(), key=lambda kv: (len(kv[0]), -kv[1]))[:60]:
    print(f'{key:10s} {c:7d}  e.g. {ex[key]}')
