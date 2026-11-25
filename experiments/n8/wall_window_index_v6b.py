"""v6b (2026-11-25): the W_1 passes whose first setter is not F's slowest reading.  Split: (A) F's slowest reading is
not blocked at t0; (B) it is blocked at t0 but a faster F reading has the larger exit (8k+1)/(8f) (E331 step-0 law:
the setter is the blocked reading with the largest exit).  Positions start at 1 (rule 5)."""
src = open('wall_window_index_v5.py').read().split("tab = Counter(); ex = {}")[0]
exec(src)
c = Counter()
def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    if not Fs: return
    a, b = t0, Fr(7, 8) / S[-1]
    moves, passed, setters, st = f_run(Fs, a, b)
    if not passed: return
    if setters[0][0] == 1: c[(pop, 'W1 pass, first setter slowest F')] += 1; return
    c[(pop, 'W1 pass, first setter not slowest', 'A slowest F not blocked at t0' if not blocked(Fs[0], t0)
       else 'B slowest blocked, faster exit larger', 'one move' if moves == 1 else 'chain')] += 1
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
import itertools, random
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]
    for g in gaps: v.append(v[-1] + g)
    for k in range(8): case('Q', readings(v, k), 0)
rng = random.Random(6); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; case('W40', [Fr(1)] + others, seen)
for k, v in sorted(c.items()): print(v, k)
