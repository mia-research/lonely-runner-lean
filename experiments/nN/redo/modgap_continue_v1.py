"""modgap_continue_v1 (2026-10-06): the continuation case E_d > t_R(T) of modgap_takeover_v2, mapped step by step.  Exact.
T minimal with cascade(T) = t*; d blocked at t* with edge E_d > t_R(T); U = T + {d}; t' = cascade(U) > E_d.
 CO1 [P] restart: running the cascade of U from the instant E_d (state t = E_d, same step rule) gives t' (the cascade from any start at or before the first
        lonely instant gives it; E_d <= t').  checked for every case.
 CO2 the blocked set B at E_d: which readings of U are in the way, classified: closers of T (at 7/8 at t_R(T)), other readings of T, d itself.
 CO3 the movers after E_d (the sequence of setters in the restart), as a pattern over the roles {c = a closer of T at t_R(T), o = other T reading, d}, and the number of
     moves; and the first mover's next-lap edge F = (8 round(x E_d) + 1)/(8x) against the landing (= t' when the chain stops there).
 CO4 the re-block count: a reading blocked at an earlier state and blocked again later (the fast-wrap case), over the restart.
Populations: the continuation cases of the first 4,000 non-unit-fraction S1 sets and of the first 4,000 of T2 (d in [1, 72] and [1, 84]).
[PROVISIONAL: counting tool; supports: the pattern counts]"""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from modgap_lib_v1 import cascade, cascade_path, openers, component, cd, E8
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
def t2():
    for r in itertools.combinations(range(2, 29), 6):
        if r[-1] >= 25: yield (1,) + r
def cascade_from(U, t):
    path = [(t, None)]
    while True:
        bl = [x for x in U if cd(x * t) < E8]
        if not bl: return path
        t, x = max((F(8 * round(x * t) + 1, 8 * x), x) for x in bl); path.append((t, x))
out = open('modgap_continue_v1.out', 'w'); out.write(__doc__ + "\n")
for name, gen, DM in (('S1', s1(), 72), ('T2', t2(), 84)):
    c = collections.Counter(); pats = collections.Counter(); ex = []; nset = 0
    for S in gen:
        if nset >= 4000: break
        t = cascade(S); tR0, _ = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR0)) >= t: continue
        nset += 1
        T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
        tR, clT = component(list(T), t)
        for d in range(1, DM + 1):
            if d in T or cd(d * t) >= E8: continue
            E = F(8 * round(d * t) + 1, 8 * d)
            if E <= tR: continue
            U = list(T) + [d]; tp = cascade(U)
            if tp == E: c['landing = E_d (no continuation)'] += 1; continue
            path = cascade_from(U, E); c[('CO1 restart from E_d gives the landing', path[-1][0] == tp)] += 1
            B = [x for x in U if cd(x * E) < E8]
            role = lambda x: 'd' if x == d else ('c' if x in clT else 'o')
            c[('CO2 blocked set at E_d', tuple(sorted(role(x) for x in B)))] += 1
            movers = tuple(role(x) for _, x in path[1:])
            pats[(min(len(movers), 5),) + movers[:5]] += 1
            seen = set(); rb = 0
            for (ti, _), (tj, _) in zip(path, path[1:]):
                for x in U:
                    if cd(x * ti) < E8:
                        if x in seen: rb += 1
                seen |= {x for x in U if cd(x * ti) < E8}
            c[('CO4 re-blocks in the restart', min(rb, 3))] += 1
            if len(path) > 2 and len(ex) < 12: ex.append((T, str(t), d, str(E), [(str(a), b) for a, b in path], str(tp)))
    out.write("\n==== %s: %d sets\n" % (name, nset))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    out.write("  CO3 (moves capped 5, mover roles in order): %s\n" % dict(sorted(pats.items(), key=lambda kv: -kv[1])))
    out.write("  examples with two or more moves after E_d: (T, t*, d, E_d, restart path, landing)\n")
    for e in ex: out.write("    %s\n" % (e,))
out.close(); print(open('modgap_continue_v1.out').read()[len(__doc__):][:6000])
