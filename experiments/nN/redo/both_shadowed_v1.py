"""E267/E268 (2026-10-02): Test 1 of log E267.  Starts: clusters whose ranks 1 and 2 are both shadowed (exact, c's run); each scaled to
c' = L*u and climbed on the 16 EightResidual predicates with ranks 1 and 2 kept shadowed at every accepted step (control: no constraint)."""
import sys, os, random, json
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
import restricted_b_v1 as R
from hole_C1_flanks_v1 import inway, study
from slow_flank_mech_v1 import state, run_us
from slow_flank_mech_v2 import valid, land_flank


def shadowed(c, cl, e):
    for u in run_us(c, e):
        if all(not inway(x, u, e) for x in cl if x != e): return False
    return True


def both(c, cl): return shadowed(c, cl, cl[0]) and shadowed(c, cl, cl[1])


def sample(seed, n=200000):
    rnd = random.Random(seed); out = []
    for _ in range(n):
        c = rnd.randrange(10**6, 10**7); span = rnd.choice((1.5, 2, 3, 5, 8, 12, 20, 40)); lo = 25 * c
        cl = sorted(rnd.randrange(lo, int(lo * span)) for _ in range(6))
        if rnd.random() < 0.5:
            cl[1] = cl[0] + int(rnd.uniform(0.02, 0.30) * c); cl.sort()
        if len(set(cl)) < 6: continue
        if shadowed(c, cl, cl[0]) and shadowed(c, cl, cl[1]) and valid(c, cl):
            out.append((c, tuple(cl)))
    return out


def scaled(item, rnd):
    c, cl = item; u = rnd.randrange(1, 20); c2 = R.L * u
    return c2, [round(F_ * c2 / c) for F_ in cl] if False else [x * c2 // c for x in cl]


def climb(c, cl0, rnd, constrained, steps=400):
    cl = list(cl0); S = lambda q: tuple(sorted([c] + q))
    score = lambda q: len(R.FIELDS) - len(R.failing(S(q))); sc = score(cl)
    for _ in range(steps):
        if sc == len(R.FIELDS): break
        o = list(cl); i = rnd.randrange(6)
        if rnd.random() < 0.5:
            m = rnd.choice((1, 2, 3, 4, 8, 16, 64, 256, 1024)); o[i] += rnd.randint(-m, m)
        else:
            mod = rnd.choice((2, 3, 4, 5, 6, 7, 8, 24, 40, 120)); o[i] = o[i] - o[i] % mod + rnd.randrange(mod)
        o.sort()
        if len(set(o)) < 6 or o[0] <= 24 * c: continue
        if constrained and not (valid(c, o) and both(c, o)): continue
        s2 = score(o)
        if s2 >= sc: cl, sc = o, s2
    return cl, sc


def job(args):
    idx, item, seed = args; rnd = random.Random(seed); runs = []
    for r in range(6):
        c, cl0 = scaled(item, rnd)
        start_ok = valid(c, cl0) and both(c, cl0)
        run = dict(start_ok=start_ok)
        for tag, cons in (('C', True), ('U', False)):
            cl, sc = climb(c, cl0, random.Random(rnd.random()), cons) if (start_ok or not cons) else (cl0, -1)
            T = tuple(sorted([c] + cl)); d = dict(score=sc, member=(sc == len(R.FIELDS)), fail=R.failing(T) if sc >= 0 else None)
            if d['member']:
                s1 = state(c, cl, cl[0])['state']; s2 = state(c, cl, cl[1])['state']
                d.update(s1=s1, s2=s2)
                if valid(c, cl):
                    lf, ts = land_flank(c, cl); d['land'] = str(lf)
                    st = study(T); d['chk'] = dict(st['chk']); d['land_ok'] = st['land_ok']
                else: d['land'] = 'invalid'
                d['T'] = T
            run[tag] = d
        runs.append(run)
    return idx, item, runs


if __name__ == '__main__':
    out = open('both_shadowed_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    with Pool(10) as pool:
        S0 = [x for part in pool.map(sample, range(20)) for x in part]
        w("starts: %d (of 4,000,000 samples); twin-pair forced starts among them: %d" % (len(S0), sum(1 for c, cl in S0 if cl[1] - cl[0] < 0.31 * c)))
        # distinct by rounded ratios
        seen = {}
        for c, cl in S0:
            key = tuple(round(x / c, 3) for x in cl)
            seen.setdefault(key, (c, cl))
        D = list(seen.values()); random.Random(1).shuffle(D); D = D[:80]
        w("distinct starts used: %d" % len(D))
        P = []
        for i, r in enumerate(pool.imap_unordered(job, [(i, it, 5000 + i) for i, it in enumerate(D)])):
            P.append(r); print('done', i + 1, flush=True)
    runs = [r for _, _, rr in P for r in rr]
    w("CHECK start states violating the constraint after scaling: %d of %d" % (sum(1 for r in runs if not r['start_ok']), len(runs)))
    for tag, name in (('C', 'CONSTRAINED (ranks 1 and 2 stay shadowed)'), ('U', 'CONTROL (no constraint)')):
        mem = [r[tag] for r in runs if r[tag]['member']]
        w("%s: members reached %d of %d runs; starts with a member %d of %d" % (name, len(mem), len(runs), sum(1 for _, _, rr in P if any(r[tag]['member'] for r in rr)), len(P)))
        w("   members: rank-1 / rank-2 states %s; landing flank %s; study CHECKS %s; landing not earliest first-clear cluster flank: %d" % (
            dict(Counter((m['s1'], m['s2']) for m in mem)), dict(sorted(Counter(m['land'] for m in mem).items())),
            dict(sum((Counter(m.get('chk', {})) for m in mem), Counter())) or '0 failures', sum(1 for m in mem if m.get('land_ok') is False)))
        fc = Counter()
        for r in runs:
            if r[tag]['fail'] is not None: fc.update(r[tag]['fail'])
        w("   field failure counts over final states: %s" % dict(fc))
        w("   final scores: %s" % dict(sorted(Counter(r[tag]['score'] for r in runs).items())))
        from slow_flank_mech_v1 import state as _st
        pats = Counter(''.join({'free': 'F', 'alone': 'A', 'handoff': 'H'}[_st(m['T'][0], list(m['T'][1:]), e)['state']] for e in m['T'][1:]) for m in mem)
        w("   six-flank patterns of the members (F free, A one walker, H hand-off; rank 1..6): %s; shadowed flanks per member: %s" % (pats.most_common(8), dict(sorted(Counter(sum(1 for ch in p if ch != 'F') for p in pats.elements()).items()))))
        if tag == 'C': json.dump([list(m['T']) for m in mem], open('both_shadowed_members_v1.json', 'w'))
        for m in mem[:3]: w("   member: %s" % (m['T'],))
    out.close(); print(open('both_shadowed_v1.out').read()[len(__doc__):])
