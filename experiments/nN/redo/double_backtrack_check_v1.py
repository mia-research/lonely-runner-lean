"""E186 (2026-09-30): independent check of the parallel session's double-and-backtrack rule
(experiments/nN/redo/double_backtrack_selector_v1.md; LRC/Spec/DoubleBacktrackN.lean).

Rule, at a dying window's pinch instant t (old labels q_i, phases f_i = d_i t - q_i in [1/8, 7/8]):
  p_i = 2 q_i + [f_i >= 9/16]  (= floor(2 d_i t - 1/8), the last opening at or before 2t),
  T = max_i (p_i + 1/8)/d_i,  delta = 2t - T,  need_i = max(0, (2 f_i - c_i - 7/8)/d_i);
  p is a window at the pinch exactly when max need <= delta; strict gives extension past the pinch.
Checked here, exactly:
  (1) the worked example: readings (1, 50, 105, 106, 136, 189, 199) on the shape path; old labels (0,0,1,1,1,2,2) at
      s* = 1990/2837, t* = 2837/7336: p, T = 41/56, delta, max need, the s-interval [199/738, 2189/2539]; and the failure
      case, old labels (0,1,2,3,4,5,6) at s = 199/483, t = 7/8.
  (2) every simple-pinch death on E178's subsampled paths (a different population from the md's 459): the rule's
      verdict (strict / equality / fails), whether p is really a window just after the pinch (exact, at tau + 10^-15),
      and the PLACE TEST: is p's window the cascade's replacement (the new first isolation just after the death)?
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
import deform_pinch_v1 as D
from deform_protect_v1 import s_interval
from quantity_tests_v1 import E8

DELTA = F(1, 10 ** 15)
_orig = D.classify


def classify_k(x, sa, ka, sb, kb):
    rec = _orig(x, sa, ka, sb, kb)
    rec['ka'], rec['kb'] = ka, kb
    return rec


D.classify = classify_k


def rule(ds, t, q):
    f = [d * t - qi for d, qi in zip(ds, q)]
    c = [1 if fi >= F(9, 16) else 0 for fi in f]
    p = tuple(2 * qi + ci for qi, ci in zip(q, c))
    T = max((pi + E8) / d for pi, d in zip(p, ds))
    delta = 2 * t - T
    need = max(max(F(0), (2 * fi - ci - F(7, 8)) / d) for fi, ci, d in zip(f, c, ds))
    return f, p, T, delta, need


def example():
    S = (1, 50, 105, 106, 136, 189, 199)
    x = [F(7 * d, S[-1]) for d in S]
    lines = []
    s = F(1990, 2837); t = F(2837, 7336); q = (0, 0, 1, 1, 1, 2, 2)
    ds = D.readings_at(x, s)
    ok, lo, hi = D.feasible(ds, q)
    f, p, T, delta, need = rule(ds, t, q)
    lines.append("worked example: old window a single instant at t*: %s (lo = hi = %s)" % (ok and lo == hi, lo))
    lines.append("  phases f = %s" % [str(v) for v in f])
    lines.append("  p = %s, T = %s, delta = %s, max need = %s, difference = %s" % (p, T, delta, need, delta - need))
    lines.append("  s-interval of p: %s" % [str(v) if v is not None else None for v in (s_interval(x, p) or (None, None))])
    s2 = F(199, 483); t2 = F(7, 8); q2 = (0, 1, 2, 3, 4, 5, 6)
    ds2 = D.readings_at(x, s2)
    ok2, lo2, hi2 = D.feasible(ds2, q2)
    f2, p2, T2, dl2, nd2 = rule(ds2, t2, q2)
    lines.append("failure case: old window a single instant at 7/8: %s; p = %s, delta = %s, max need = %s -> %s" %
                 (ok2 and lo2 == hi2 == t2, p2, dl2, nd2, "fails" if nd2 > dl2 else "passes"))
    return lines


def study(S):
    S = tuple(sorted(S)); x = [F(7 * d, S[-1]) for d in S]
    r = D.follow(S)
    rows = []
    for e in r['events']:
        if e.get('kind') != 'death' or e.get('tau') is None or e['tau'] == 0 or not e['simple']:
            continue
        tau, t0, q = e['tau'], e['t0'], e['ka']
        ds = D.readings_at(x, tau)
        f, p, T, delta, need = rule(ds, t0, q)
        verdict = 'strict' if need < delta else ('equal' if need == delta else 'fails')
        after = D.feasible(D.readings_at(x, tau + DELTA), p)[0]
        rows.append(dict(verdict=verdict, after=after, is_repl=(p == e['kb']),
                         earlier=(T < t0), R_T=float(8 * min(ds) * T), R0=float(8 * min(ds) * t0)))
    return rows


if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    out = open('double_backtrack_check_v1.out', 'w'); out.write(__doc__ + "\n")
    for line in example():
        out.write(line + "\n")
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]][::400]
    rng = random.Random(13); caseC = []
    while len(caseC) < 500:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            caseC.append(T)
    with Pool(8) as pool:
        for name, sets in [('Case B every 400th', caseB), ('late every 40th', late_shapes()[::40]), ('Case C first 100', caseC[:100])]:
            rows = [x for rs in pool.map(study, sets) for x in rs]
            v = Counter(x['verdict'] for x in rows)
            out.write("\n== %s: simple-pinch deaths %d ==\n" % (name, len(rows)))
            out.write("  rule verdict: strict %d, equality %d, fails %d\n" % (v['strict'], v['equal'], v['fails']))
            out.write("  CHECK strict => p is a window just after the pinch: %d of %d\n" %
                      (sum(x['after'] for x in rows if x['verdict'] == 'strict'), v['strict']))
            out.write("  CHECK fails => p is not a window just after: %d of %d\n" %
                      (sum(not x['after'] for x in rows if x['verdict'] == 'fails'), v['fails']))
            out.write("  PLACE TEST: p's window is the cascade's replacement: %d of %d strict (and %d of all deaths)\n" %
                      (sum(x['is_repl'] for x in rows if x['verdict'] == 'strict'), v['strict'], sum(x['is_repl'] for x in rows)))
            out.write("  p's window earlier than the dying instant: %d of %d strict\n" %
                      (sum(x['earlier'] for x in rows if x['verdict'] == 'strict'), v['strict']))
    out.close()
    print(open('double_backtrack_check_v1.out').read()[len(__doc__):])
