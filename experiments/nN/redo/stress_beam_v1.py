# stress_beam_v1.py -- constructive beam search (exact).  Start {1}; add one reading per level (6 levels) so that the new reading's zone
#   (type 1) contains the current landing L with its EXIT tied (1+eps) to an entry of an existing reading, or
#   (type 2) has its ENTRY just before an existing path state R_s (blocks it).
# The landing of a parent set is the cascade's first clear point (exact, monotone non-decreasing as readings are added).
# Score = exact landing of the 7-reading set (levels < 6 give partial sets with fewer readings).  Floats are not used for facts.
# usage: python3 stress_beam_v1.py SECONDS SEED CAP WIDTH PERPARENT
import sys; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
from collections import Counter
T0 = time.time(); LIM = float(sys.argv[1]); rnd = random.Random(int(sys.argv[2])); CAP = F(sys.argv[3]); W = int(sys.argv[4]); PP = int(sys.argv[5])
def land(rs):
    steps, R = fpath([Q(x) for x in rs]); return steps, R
def children(rs):
    steps, L = land(rs); L = Fr(L); out = {}
    states = {Fr(s[0]) for s in steps} | {Fr(s[3]) for s in steps} | {L}
    eps = F(1, 10 ** rnd.choice((6, 9, 12)))
    cands = []
    for x in rs:                                  # type 1
        for i in range(1, 80):
            e = (8 * i - 1) / x
            if e <= L: continue
            if e > 26: break
            e2 = e * (1 + eps)
            js = [j for j in range(1, int(float(CAP * e2) / 8) + 2) if 1 < (8 * j + 1) / e2 <= CAP and (8 * j - 1) / ((8 * j + 1) / e2) < L]
            if js: cands += [(8 * j + 1) / e2 for j in (rnd.sample(js, min(len(js), PP // 6)))]
            if i > 3 and e > L * 1.5: break
    for Rs in states:                             # type 2
        js = [j for j in range(1, int(float(CAP * Rs) / 8) + 2) if 1 < (8 * j - 1) / Rs * (1 + eps) <= CAP]
        if js: cands += [(8 * j - 1) / Rs * (1 + eps) for j in rnd.sample(js, min(len(js), max(2, PP // 12)))]
    rnd.shuffle(cands)
    for y in cands:
        if y in rs: continue
        new = tuple(sorted(rs + (y,)))
        if new in out: continue
        st, R = land(new); out[new] = (Fr(R), len(st))
    return out
beam = {(F(1),): (F(1), 0)}; best = {}
for level in range(1, 7):
    pool = {}
    for rs in list(beam)[:W]:
        if time.time() - T0 > LIM: break
        pool.update(children(rs))
    if not pool: break
    # diversity: keep top by landing, tie by number of moves
    ranked = sorted(pool.items(), key=lambda kv: (-kv[1][0], -kv[1][1]))
    beam = dict(ranked[:W]); best[level] = ranked[0]
    print('level', level, 'pool', len(pool), 'beam landing max', float(ranked[0][1][0]), 'moves', ranked[0][1][1], 'elapsed', round(time.time() - T0), flush=True)
rs, (L, ns) = best[max(best)]
print('args', sys.argv[1:]); print('best exact landing', L, float(L), 'readings', len(rs), [str(x) for x in rs])
if len(rs) == 7:
    cl, R, v, o = check([Q(x) for x in rs]); print('class', cl, 'violations', v, 'opener', o['opener'], 'closer', o['closer'], 'moves', o['nm'])
    oo = OFFICIAL_outcome(list(rs)); print('official landing equals:', oo['R'] == L)
    print('rho_7', float(rs[6]), 'rho_6', float(rs[5]))
cnt = Counter()
for rs2, (L2, n2) in list(beam.items()):
    if len(rs2) == 7:
        cl, R, v, o = check([Q(x) for x in rs2]); cnt[cl] += 1
        for s in v: cnt['VIOL ' + s.split(':')[0]] += 1
print('beam members checked', dict(cnt))
print('beam top 5 landings', [float(v[0]) for v in list(beam.values())[:5]], 'rho_7 of top 5', [float(k[-1]) for k in list(beam)[:5]])
