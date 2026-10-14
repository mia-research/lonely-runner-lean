"""E263/E264 (2026-10-02): the restricted (b) -- for a C1-shaped set in EightResidual, the cluster's fastest flank is not
hand-off-shadowed across c's band run -- tested three ways.  Design: log E263.

Part 1: E118's construction (residual_members_C_v1.py), unchanged, under seeds 201-210, modes A and B; the fastest flank's
state on every member (redo/hole_C1_flanks_v1.flank), and the near-twin chain when it is shadowed.
Part 2: every EightResidual field predicate failed by each of E262's 58 C1-shaped sets (1, K*six).
Part 3: each of the 58 hand-off shapes built toward membership by E118's method: c = L*u, cluster K*six in [25c, 175c],
small integer adjustments climbing on fields passed, the fastest flank kept hand-off-shadowed at every accepted step.
Checks: members re-checked on all 16 predicates; the cascade's landing lonely.
"""
import sys, json, random, math, re
from collections import Counter
from fractions import Fraction as F
from multiprocessing import Pool
exec(open('residual_fields_v1.py').read())
sys.path.insert(0, 'redo'); sys.path.insert(0, 'band_cert_v1')
from hole_C1_flanks_v1 import flank
from e151_block_v1 import trace
from quantity_tests_v1 import cd, E8

SRC = open('residual_members_C_v1.py').read().split("# through the cascade, exact")[0]
SRC = SRC.replace("exec(open('residual_fields_v1.py').read())", "").replace("rnd = random.Random(118)", "rnd = random.Random(SEED)")


def construct(seed):
    g = dict(globals()); g['SEED'] = seed
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        exec(SRC, g)
    return [('A', tuple(S)) for S in g['found']['A']] + [('B', tuple(S)) for S in g['found']['B']]


def allfields(S):
    return [n for n, f in FIELDS if not f(S)]


def chain_from_fastest(S):
    S = tuple(sorted(S)); c = S[0]; cl = list(S[1:]); e = cl[-1]; st = flank(c, cl, e); links = []
    while st['state'] == 'alone' and len(links) < 7:
        links.append(st['walker'])
        e = cl[st['walker'][0] - 1]; st = flank(c, cl, e)
    return st['state'], links


def part1(seed):
    out = []
    for mode, S in construct(seed):
        bad = allfields(S)
        st = flank(S[0], list(S[1:]), S[-1])['state']
        end, links = chain_from_fastest(S) if st != 'free' else ('free', [])
        out.append((seed, mode, S, bad, st, end, links))
    return out


def lonely(S, t):
    return all(cd(d * t) >= E8 for d in S)


def part3(args):
    six, seed = args
    rnd = random.Random(seed)
    for restart in range(6):
        u = rnd.randrange(1, 20); c = L * u
        K = -(-25 * c // six[0]) * rnd.choice((1, 2, 3, 5))
        cl = [K * x for x in six]
        if cl[-1] > 175 * c * 6:
            continue
        S = tuple(sorted([c] + cl))
        if flank(c, cl, cl[-1])['state'] != 'handoff':
            continue
        sc = sum(1 for n, f in FIELDS if f(S))
        for step in range(400):
            i = rnd.randrange(6); o = list(cl)
            o[i] = o[i] + rnd.choice((-1, 1)) * rnd.randrange(1, 4000)
            if len(set(o)) < 6 or sorted(o) != o or o[0] <= c:
                continue
            if flank(c, o, o[-1])['state'] != 'handoff':
                continue
            T = tuple(sorted([c] + o)); s2 = sum(1 for n, f in FIELDS if f(T))
            if s2 >= sc:
                cl, S, sc = o, T, s2
            if sc == len(FIELDS):
                ts, _ = trace(S)
                h = next(x for x in S if (8 * x * ts) % 8 == 1)
                return dict(six=six, found=True, S=S, lonely=lonely(S, ts), land=(S.index(h), float(8 * c * ts)))
    return dict(six=six, found=False, best=sc)


if __name__ == '__main__':
    out = open('restricted_b_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    with Pool(8) as pool:
        p1 = [x for part in pool.map(part1, range(201, 211)) for x in part]
    w("== Part 1: E118's construction, seeds 201-210: %d members ==" % len(p1))
    w("  members failing any predicate on re-check: %d" % sum(1 for x in p1 if x[3]))
    w("  the fastest flank: %s" % dict(Counter((x[1], x[4]) for x in p1)))
    w("  shadowed fastest flanks: chain ends: %s; chain lengths: %s" % (dict(Counter(x[5] for x in p1 if x[4] != 'free')), dict(Counter(len(x[6]) for x in p1 if x[4] != 'free'))))
    for x in p1:
        if x[4] == 'handoff':
            w("  COUNTEREXAMPLE seed %d mode %s: %s" % (x[0], x[1], x[2]))
    six58 = [tuple(int(v) for v in m.group(1).split(',')) for m in re.finditer(r"six \(([0-9, ]+)\)", open('redo/fastest_flank_check_v1.out').read())]
    w("\n== Part 2: the 58 C1-shaped sets (1, K*six): failing predicates ==")
    prof = Counter(); every = None
    for six in six58:
        K = -(-9 // six[0]); S = tuple([1] + [K * x for x in six])
        bad = allfields(S); prof.update(bad)
        every = set(bad) if every is None else every & set(bad)
        w("  six %s K %d: fails %s" % (six, K, bad))
    w("  predicates failed, counted over the 58: %s" % dict(prof.most_common()))
    w("  predicates failed by all 58: %s" % (sorted(every) if every else 'none'))
    with Pool(8) as pool:
        p3 = pool.map(part3, [(six, 263 + i) for i, six in enumerate(six58)])
    found = [r for r in p3 if r['found']]
    w("\n== Part 3: each hand-off shape built toward membership (fastest flank kept hand-off-shadowed): %d shapes ==" % len(p3))
    w("  members of EightResidual found with a hand-off-shadowed fastest flank: %d" % len(found))
    for r in found:
        w("  COUNTEREXAMPLE six %s -> S %s; lonely at the cascade's landing: %s; lands at index %d, R* = %.4f; re-check fails: %s" % (
            r['six'], r['S'], r['lonely'], r['land'][0], r['land'][1], allfields(r['S'])))
    w("  not found: best predicates passed per shape: %s" % dict(Counter(r['best'] for r in p3 if not r['found'])))
    out.close()
    print(open('restricted_b_v1.out').read()[len(__doc__):][:8000])
