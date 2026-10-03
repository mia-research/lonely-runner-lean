# stress_exceed_v1.py -- part 3: lap-triple family  R* = 9 (8a+1)(8b+1) / ((8c1-1)(8c2-1))  (extremal: a=11, b=4, c1=c2=6).
# Construction (exact): rho_5 = (8c1-1)/9 (1+e1)   [reading 5 blocked at the gate state R=9, lap c1]
#                       R17   = (8b+1)/rho_5        [exit of reading 5 lap b]
#                       rho_7 = (8c2-1)/R17 (1+e2)  [reading 7 blocked at R17, lap c2]
# the four other readings are searched (exact evaluation; aimed moves; floats only choose acceptance) to realise the opener (7,a).
# usage: python3 stress_exceed_v1.py SECONDS_PER_TRIPLE SEED MAXTRIPLES MODE(equal|diff)
import sys, math, pickle; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
from collections import Counter
T0 = time.time(); PER = float(sys.argv[1]); rnd = random.Random(int(sys.argv[2])); MAXT = int(sys.argv[3]); MODE = sys.argv[4]
(x0,) = pickle.load(open('b12_A_x0_v1.pkl', 'rb')); X0 = [F(x) for x in x0]
SUP = F(26433, 2209)
def eps(): return F(1, 10 ** rnd.randint(2, 11))
tr = []
for c1 in range(2, 13):
    for c2 in range(2, 13):
        if (MODE == 'equal') != (c1 == c2): continue
        for b in range(1, 25):
            for a in range(2, 60):
                V = F(9 * (8 * a + 1) * (8 * b + 1), (8 * c1 - 1) * (8 * c2 - 1))
                rho5 = F(8 * c1 - 1, 9); R17 = (8 * b + 1) / rho5
                if V > SUP and V < 24 and R17 > 1 and R17 < V and rho5 > 1: tr.append((V, a, b, c1, c2))
tr.sort(key=lambda t: t[0]); rnd.shuffle(tr); tr = tr[:MAXT]
print('triples with formula > 26433/2209 (and < 24, 1 < R17 < V):', len(tr), 'mode', MODE)
res = []; viol = Counter(); allbest = (F(0), None, None)
def evaluate(r):
    r = sorted(r)
    if r[0] != 1 or len(set(r)) != 7: return None
    rh = [Q(x) for x in r]; cl, R, v, o = check(rh)
    for s in v: viol[s.split(':')[0].split('_step')[0]] += 1
    return Fr(R), o, cl, v, r
for (V, a, b, c1, c2) in tr:
    rho5 = F(8 * c1 - 1, 9) * (1 + eps()); R17 = (8 * b + 1) / rho5; rho7 = (8 * c2 - 1) / R17 * (1 + eps())
    if rho7 <= 1: continue
    t0 = time.time(); best = None; n = 0
    while time.time() - t0 < PER:
        if best is None or rnd.random() < 0.05:
            free = [X0[1], X0[2], X0[3], X0[5]] if rnd.random() < .5 else [F(rnd.randint(105, 2400), 100) for _ in range(4)]
            free = [f * (1 + rnd.choice((-1, 1)) * eps()) for f in free]
            cr0 = evaluate([F(1), rho5, rho7] + free)
            if cr0 is None: continue
            cur = free; cr = cr0
            curv = float(cr[0]); n += 1
            if best is None or cr[0] > best[0][0]: best = (cr, list(cur))
        new = list(cur); t = rnd.random(); y = rnd.randrange(4)
        if t < 0.3: new[y] *= 1 + rnd.choice((-1, 1)) * F(1, 10 ** rnd.randint(1, 8))
        elif t < 0.4: new[y] = F(rnd.randint(105, 2400), 100)
        else:
            rr = [Q(x) for x in cr[4]]; sp, _ = fpath(rr)
            if not sp: continue
            s = rnd.choice(sp); pt = Fr(rnd.choice((s[0], s[3]))); i = max(1, round((pt * new[y] + rnd.choice((-1, 1))) / 8))
            new[y] = (8 * i + rnd.choice((-1, 1))) / pt * (1 + rnd.choice((-1, 0, 1)) * eps())
        if new[y] <= 1: continue
        e = evaluate([F(1), rho5, rho7] + new); n += 1
        if e is None: continue
        if float(e[0]) >= curv or rnd.random() < math.exp((float(e[0]) - curv) / 0.2):
            cur, cr, curv = new, e, float(e[0])
        if e[0] > best[0][0]: best = (e, list(new))
        if e[0] > SUP: print('EXCEEDS', e[0], [str(x) for x in e[4]])
    (R, o, cl, v, r), fr = best
    prem_gate = any(s[3] == 9 for s in fpath([Q(x) for x in r])[0])
    prem_R17 = any(Fr(s[3]) == R17 or abs(Fr(s[3]) - R17) < F(1, 10**6) for s in fpath([Q(x) for x in r])[0])
    res.append((V, a, b, c1, c2, R, o['opener'], cl, prem_gate, prem_R17, n))
    if R > allbest[0]: allbest = (R, r, (V, a, b, c1, c2))
    if time.time() - T0 > 520: break
print('triples run', len(res), 'seconds', round(time.time() - T0))
print('exact best landing over all triples:', allbest[0], float(allbest[0]), [str(x) for x in allbest[1]], 'triple (V,a,b,c1,c2)', [str(x) for x in allbest[2]])
print('violations of G/C/S/class in all evaluations:', dict(viol))
gate = Counter(); opn = Counter(); stop = Counter()
for (V, a, b, c1, c2, R, op, cl, pg, pR, n) in res:
    gate[pg] += 1; opn[op == (7, a)] += 1
    stop[('gate' if pg else 'no_gate', 'R17in' if pR else 'R17out', 'opener=(7,a)' if op == (7, a) else 'opener_other', 'landing<V' if R < V else 'landing>=V')] += 1
print('premise breakdown (best arrangement per triple):'); [print(' ', k, v) for k, v in sorted(stop.items(), key=lambda kv: -kv[1])]
print('per triple (V a b c1 c2 | best landing | opener | class | gate | R17 | evals), top 25 by landing:')
for t in sorted(res, key=lambda t: -t[5])[:25]: print(' ', float(t[0]), t[1:5], float(t[5]), t[6], t[7], t[8], t[9], t[10])
