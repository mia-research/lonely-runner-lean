"""n=5, own-AP instants.  At the subject's own-AP instant n' (R = n'), runner x with reading s = a + e sits at drift
position n'*a + n'*e (mod 5); it is in the way iff that is within 1 of a multiple of 5 (own-AP residue rule).
(1) exact AP readings (e = 0): R_final for index triples;  (2) for high-R arrangements: who is in the way at R = 1, 2, 3
and at the last iterate, with residues and drift;  (3) over many arrangements: R_final against which own-AP instants the
chain passes and by whom."""
from fractions import Fraction as F
import math, random, itertools, collections
def near(x): return math.floor(x + F(1, 2))
def cascade(s):
    R = F(1); steps = []
    while True:
        best = R; who = None
        for i, sx in enumerate(s):
            v = sx * R; N = near(v / 5)
            if abs(v - 5 * N) < 1:
                cand = F(5 * N + 1) / sx
                if cand > best: best, who = cand, (i, N)
        if who is None: return R, steps
        steps.append((who[0], who[1], best)); R = best
def inway_at(s, R):
    return [i for i, sx in enumerate(s) if abs(sx * R - 5 * near(sx * R / 5)) < 1]
print('(1) exact AP readings: final R')
res = collections.Counter()
for tri in itertools.combinations_with_replacement(range(2, 21), 3):
    if len(set(tri)) < 3: continue
    R, _ = cascade([F(x) for x in tri])
    res[R] += 1
print('   distribution of R over exact index triples in 2..20:', {str(k): v for k, v in sorted(res.items())})
print('   max', max(res), '— the chain from R = 1 with exact AP readings')
# (2) high-R arrangements from the previous search
tops = [[F('2.2415'), F('3.27951'), F(9)], [F('1.7799'), F('2.6686'), F('4.0012')], [F('2.58777'), F('3.27273'), F(4)],
        [F('2.2402'), F('3.27273'), F(4)]]
print('\n(2) own-AP instants in high-R cascades')
for s in tops:
    R, steps = cascade(s)
    print(f'   readings {[float(x) for x in s]}  R_final {float(R):.4f}')
    for nprime in (1, 2, 3, 4):
        if nprime < R:
            iw = inway_at(s, F(nprime))
            det = [f"{'bcd'[i]}: {nprime}·{float(s[i]):.4f} = {float(nprime * s[i]):.4f}" for i in iw]
            print(f'      R = {nprime}: in the way {det}')
# (3) statistics: R_final vs instants passed
rng = random.Random(3)
bins = collections.defaultdict(lambda: [0, collections.Counter()])
for _ in range(200000):
    s = sorted(1 + F(rng.randint(0, 10**5), 10**4) for _ in range(3))
    if len(set(s)) < 3: continue
    R, steps = cascade(s)
    passed = sum(1 for nprime in (2, 3) if R > nprime)
    b = bins[passed]; b[0] += 1
    if passed:
        # which runners cover the instants passed: record the set of AP residues a mod 5 of those runners
        for nprime in (2, 3)[:passed]:
            for i in inway_at(s, F(nprime)):
                b[1][(nprime, near(s[i]) % 5)] += 1
print('\n(3) chains by own-AP instants passed (of 2, 3), readings uniform in [1, 11]:')
for k in sorted(bins):
    print(f'   passed {k}: {bins[k][0]} chains; in-way runners at those instants by (instant, index mod 5): {dict(bins[k][1].most_common(12))}')
