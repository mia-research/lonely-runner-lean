"""E263/E264 (2026-10-02): the restricted (b) tested three ways.  Design: log E263.

(b) restricted to EightResidual: for a C1-shaped set in EightResidual, the cluster's fastest flank is not hand-off-shadowed
across c's band run (hole_C1_flanks_v1.flank: state 'handoff').

Part 1: E118's construction (residual_members_C_v1.py, unchanged) under seeds 201..210; every member read by
        hole_C1_flanks_v1.study; counterexamples = members whose fastest flank is a hand-off.
Part 2: the 58 C1-shaped sets (1, K*six) of E262 (parsed from fastest_flank_check_v1.out): every one of the 16 field
        predicates (residual_fields_v1.FIELDS) each fails.
Part 3: the 58 shapes built toward membership: c = L*u, cluster K*six with K*x1 in [25c, 175c], cluster readings adjusted
        by integers, climbing on the number of fields passed, the fastest flank's hand-off kept as a constraint at every
        accepted step.  Control: the same climb from the same starts with the constraint removed.
Checks: every member re-checked on all 16 predicates; c never in the way inside its run; the landing is the earliest
first-clear cluster-flank opening and the set is lonely there (study's checks); the start state of every Part 3 shape
satisfies the constraint.
"""
import sys, os, re, io, random, contextlib, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); NN = os.path.dirname(HERE)
os.chdir(HERE)
sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
from hole_C1_flanks_v1 import study, flank


class in_nn:
    def __enter__(self): os.chdir(NN)
    def __exit__(self, *a): os.chdir(HERE)


with in_nn():
    _ns = {}
    exec(open(NN + '/residual_fields_v1.py').read(), _ns)
FIELDS = _ns['FIELDS']; L = _ns['L']
NAMES = [n for n, _ in FIELDS]


def failing(S):
    return [n for n, f in FIELDS if not f(S)]


# ---------------- Part 1 ----------------
def part1_seed(seed):
    src = open(NN + '/residual_members_C_v1.py').read().split("# through the cascade")[0]
    assert 'random.Random(118)' in src
    src = src.replace('random.Random(118)', 'random.Random(%d)' % seed)
    ns = {}
    with in_nn(), contextlib.redirect_stdout(io.StringIO()):
        exec(src, ns)
    found = ns['found']
    rows = []
    for mode in 'AB':
        for S in found[mode]:
            r = study(S)
            rows.append(dict(seed=seed, mode=mode, S=tuple(sorted(S)), fast=r['fast'], chk=dict(r['chk']), land_ok=r['land_ok'],
                             nfail=len(failing(tuple(sorted(S)))), detail=r['fast_detail']))
    return rows


# ---------------- Part 2 ----------------
def parse58():
    out = []
    for line in open(HERE + '/fastest_flank_check_v1.out'):
        m = re.match(r'\s+six \(([\d, ]+)\)\s+K (\d+):', line)
        if m:
            out.append((tuple(int(x) for x in m.group(1).split(',')), int(m.group(2))))
    return out


def part2_one(item):
    six, K = item
    T = tuple([1] + [K * x for x in six])
    return six, K, failing(T)


# ---------------- Part 3 ----------------
def fast_state(c, cl):
    e = max(cl)
    return flank(c, cl, e)['state']


def climb(c, cl0, rnd, constrained, steps=400):
    cl = list(cl0)
    S = lambda cl_: tuple(sorted([c] + cl_))
    score = lambda cl_: len(FIELDS) - len(failing(S(cl_)))
    sc = score(cl)
    for _ in range(steps):
        if sc == len(FIELDS):
            break
        o = list(cl); i = rnd.randrange(6)
        if rnd.random() < 0.5:
            m = rnd.choice((1, 2, 3, 4, 8, 16, 64, 256, 1024)); o[i] = o[i] + rnd.randint(-m, m)
        else:
            mod = rnd.choice((2, 3, 4, 5, 6, 7, 8, 24, 40, 120)); o[i] = o[i] - o[i] % mod + rnd.randrange(mod)
        if len(set(o)) < 6 or min(o) <= 24 * c or o[i] <= 0:
            continue
        if constrained and fast_state(c, o) != 'handoff':
            continue
        s2 = score(o)
        if s2 >= sc:
            cl, sc = o, s2
    return cl, sc


def part3_shape(item):
    idx, six, seed = item
    rnd = random.Random(seed)
    res = dict(six=six, runs=[])
    for r in range(6):
        u = rnd.randrange(1, 20); c = L * u
        lo = -(-25 * c // six[0]); hi = (175 * c) // six[0]
        K = rnd.randrange(lo, hi + 1)
        cl0 = [K * x for x in six]
        start_ok = fast_state(c, cl0) == 'handoff'
        run = dict(u=u, start_ok=start_ok)
        for tag, cons in (('C', True), ('U', False)):
            cl, sc = climb(c, cl0, random.Random(rnd.random()), cons)
            T = tuple(sorted([c] + cl))
            run[tag] = dict(score=sc, member=(sc == len(FIELDS)), fail=failing(T), fast=fast_state(c, cl))
            if sc == len(FIELDS):
                st = study(T)
                run[tag]['study'] = dict(chk=dict(st['chk']), land_ok=st['land_ok'], T=T)
        res['runs'].append(run)
    return res


if __name__ == '__main__':
    out = open('restricted_b_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    w("fields (%d): %s\n" % (len(FIELDS), NAMES))

    # Part 1
    with Pool(10) as pool:
        P1 = [r for part in pool.map(part1_seed, range(201, 211)) for r in part]
    w("== PART 1: E118's construction, seeds 201..210 ==")
    for mode in 'AB':
        R = [r for r in P1 if r['mode'] == mode]
        ck = Counter()
        for r in R:
            ck.update(r['chk'])
        w("  mode %s: %d members; fields failing on re-check: %d; CHECKS: %s; landing not earliest first-clear cluster flank: %d" % (
            mode, len(R), sum(1 for r in R if r['nfail']), dict(ck) if ck else '0 failures', sum(1 for r in R if not r['land_ok'])))
        w("    fastest flank state: %s" % dict(Counter(r['fast'] for r in R)))
    ce = [r for r in P1 if r['fast'] == 'handoff']
    w("  COUNTEREXAMPLES to the restricted (b) (fastest flank a hand-off): %d" % len(ce))
    for r in ce[:20]:
        w("    seed %d mode %s: %s  %s" % (r['seed'], r['mode'], r['S'], r['detail']))

    # Part 2
    P58 = parse58()
    w("\n== PART 2: the %d counterexample shapes of E262, all 16 field predicates ==" % len(P58))
    with Pool(8) as pool:
        P2 = pool.map(part2_one, P58)
    cnt = Counter()
    for six, K, fl in P2:
        cnt.update(fl)
        w("  six %s K %d fails %d: %s" % (six, K, len(fl), fl))
    w("  failing counts per field (of %d): %s" % (len(P2), {n: cnt.get(n, 0) for n in NAMES}))
    allfail = [n for n in NAMES if cnt.get(n, 0) == len(P2)]
    w("  fields failed by ALL %d: %s" % (len(P2), allfail))
    only = Counter(tuple(fl) for _, _, fl in P2)
    w("  distinct failing-field sets: %d; the ten most common: %s" % (len(only), only.most_common(10)))

    # Part 3
    w("\n== PART 3: the 58 shapes built toward membership (c = L*u, cluster K*six + integer adjustments, 6 restarts x 400 steps) ==")
    with Pool(8) as pool:
        P3 = pool.map(part3_shape, [(i, six, 3000 + i) for i, (six, K) in enumerate(P58)])
    ok0 = sum(1 for s in P3 for r in s['runs'] if not r['start_ok'])
    w("  CHECK start states violating the constraint: %d of %d" % (ok0, 6 * len(P3)))
    for tag, name in (('C', 'CONSTRAINED (fastest flank stays a hand-off)'), ('U', 'CONTROL (no constraint)')):
        mem = [(s['six'], r) for s in P3 for r in s['runs'] if r[tag]['member']]
        w("  %s: members reached %d of %d runs; shapes with a member %d of %d" % (
            name, len(mem), 6 * len(P3), len({six for six, r in mem}), len(P3)))
        ck = Counter(); lo_bad = 0
        for six, r in mem:
            ck.update(r[tag]['study']['chk']); lo_bad += (not r[tag]['study']['land_ok'])
        w("    members' CHECKS: %s; landing not earliest first-clear cluster flank: %d" % (dict(ck) if ck else '0 failures', lo_bad))
        if tag == 'U':
            w("    control members whose fastest flank is still a hand-off: %d; fastest-flank states: %s" % (
                sum(1 for six, r in mem if r['U']['fast'] == 'handoff'), dict(Counter(r['U']['fast'] for six, r in mem))))
        best = Counter()
        for s in P3:
            b = min((r for r in s['runs']), key=lambda r: len(r[tag]['fail']))
            best[tuple(b[tag]['fail'])] += 1
        w("    best run per shape, fields still failing: %s" % best.most_common(12))
        fcount = Counter()
        for s in P3:
            for r in s['runs']:
                fcount.update(r[tag]['fail'])
        w("    field failure counts over all %d final states: %s" % (6 * len(P3), {n: fcount.get(n, 0) for n in NAMES}))
    out.close()
    print(open('restricted_b_v1.out').read()[len(__doc__):])
