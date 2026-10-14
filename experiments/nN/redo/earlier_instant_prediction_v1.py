"""E383 (2026-10-05), earlier_instant_prediction_v1: the 'earlier instant' crossings of E219 B, perturbed.

Owner: "do that and perturb the exceptions" (the relocation rule: a deviation moves the isolation; E219: a leaving face is a
hand-off, an entering face displaces it to the entering reading's next exit; the exceptions are the crossings where the new
landing is EARLIER than the old one, 306 of 1,800 whole-number and 281 of 1,800 fine-shape entering crossings, 153 and 106 for
leaving crossings).

CLASS: E219 B's populations, same seeds (300 sets from the readings <= 16 family: rng 218; 300 fine shapes: seed 220), same
construction (arrangement scaled by L = 1000 (8K+1), reading d moved one unit past its leaving or entering edge).
PREDICTION (derived before the run, in the carving's terms): a speed change moves every zone of the changed reading d
(its zone j is ((8j-1)/d, (8j+1)/d)) not only the one at the landing.  So an earlier landing t' < t appears exactly when, in
the OLD arrangement, t' was blocked by d alone, i.e. t' lay in one zone of d and no other reading's zone, and d's moved
zone edge crossed t'.  The prediction to test, exactly: in every 'earlier instant' crossing, the set of readings in the way
at the new landing t' under the OLD arrangement equals {d}.  Misses are listed individually and are the perturbation
targets.  Side of d at t' in the old arrangement is recorded (position in eighths below 1, i.e. just before its exit:
'leaving side'; above 7: 'entering side').
Exact (Fractions, integers); the readings in the way use cd(x t) < 1/8 as in E219.
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
import persistence_run_v1 as P
from quantity_tests_v1 import cd, E8

Q = P.Q


def study(S):
    S = tuple(sorted(S))
    ts, h, K, laps, c1, _ = P.cert(S)
    L = Q * (8 * K + 1); t = F(8 * K + 1, 8 * h * L); base = [x * L for x in S]
    rows = []
    for d in S:
        if d == h:
            continue
        k = laps[d][0]
        for face in ('leaving', 'entering'):
            dv = (8 * k + 1) * h * Q - 1 if face == 'leaving' else (8 * k + 7) * h * Q + 1
            U = [x for x in base if x != d * L] + [dv]
            if len(set(U)) < 7 or min(U) <= 0:
                continue
            U = tuple(sorted(U))
            ts2, h2, K2, laps2, c12, nm2 = P.cert(U)
            if not (ts2 < t):
                continue
            # new landing ts2 (in U's time); old arrangement base at the same time
            way_old = [x for x in base if cd(x * ts2) < E8]
            pos = (8 * d * L * ts2) % 8
            side = 'leaving side (p<1)' if pos < 1 else ('entering side (p>7)' if pos > 7 else 'inside band?')
            ok = (way_old == [d * L])
            way_names = ['d' if x == d * L else 'other' for x in way_old]
            rows.append(dict(face=face, ok=ok, side=side, nway=len(way_old), names=tuple(sorted(way_names)), S=S, d=d))
    return rows


if __name__ == '__main__':
    out = open('earlier_instant_prediction_v1.out', 'w'); out.write(__doc__ + "\n")
    rng = random.Random(218)
    p1 = list(itertools.combinations(range(1, 17), 7))
    b1 = rng.sample(p1, 300); b2 = P.fine(220, 300, 2, 20)
    with Pool(4) as pool:
        for name, sets in [('300 sets from the readings <= 16 family', b1), ('300 fine shapes, spread in [2, 20]', b2)]:
            rows = [r for rs in pool.map(study, sets) for r in rs]
            out.write("\n== %s: earlier-instant crossings %d ==\n" % (name, len(rows)))
            for face in ('leaving', 'entering'):
                rr = [r for r in rows if r['face'] == face]
                out.write("  %s face: %d crossings; prediction holds (readings in the way at the new landing, old arrangement = {d}): %d; misses %d\n" % (
                    face, len(rr), sum(r['ok'] for r in rr), sum(not r['ok'] for r in rr)))
                out.write("    side of d at the new landing in the old arrangement: %s\n" % dict(Counter(r['side'] for r in rr if r['ok'])))
                out.write("    miss patterns (number in the way, who): %s\n" % dict(Counter((r['nway'], r['names']) for r in rr if not r['ok']).most_common(12)))
            out.flush()
    out.close()
    print(open('earlier_instant_prediction_v1.out').read()[len(__doc__):])
