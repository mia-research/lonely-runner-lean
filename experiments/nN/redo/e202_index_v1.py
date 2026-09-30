"""E202 (2026-09-30): what decides the index (E201): designed in AP/grid-plus-deviation terms, then run against the cascade.

Owner: "yes, design what decides the index first, then run it.  remember our checklist to make sure we're not
drifting.  Why ap/grid plus deviation works to find the isolation everytime".

DESIGN (units R = 8 d_min t; P = the slow part, spread sigma <= 7; F = the fast part; E201's split)
  1. The start is always there.  At the bound R = 1 the slow part is clear (every p/d_min in [1, sigma] with sigma <= 7,
     slots 1..6 of the eighths: AP-like), and the instant is the class-1 instant of the slowest reading's own grid: each
     fast reading f sits at eighth-slot floor(f/d_min) mod 8 with deviation frac(f/d_min).  So at the start the only
     obstruction is the fast readings the deviation has put in the subject's slot: the CAPTURES.  [derived]
  2. The push.  The cascade separates the captures (each move is the latest exit among those in the slot); during each
     separation, readings near the entering edge can be CARRIED IN (`transport`: only readings carried over the entering
     edge obstruct next).  Inside P's first clear interval R in [1, 7/sigma] every move is F's (E201, D1).  [derived]
  3. What decides the index.  Derived exactly: the landing is in P's first interval iff F's push ends by R = 7/sigma.
     So the index is decided by the push's EXTENT (captures separating, carry-ins, read from the grid slots and deviations
     at the start) against P's interval end 7/sigma.  The derived equivalence is a check, not a finding (M4).
  Why AP/grid plus deviation finds the isolation (the design's claim to test): at the start the AP-like slow part is
  clear and the fast part is a grid plus deviation; the isolation is where the separations of what the deviation captured
  stop carrying anyone in.

CHECKLIST (applied to this design; recorded so drift is visible):
  object = the cascade's own run (captures, separations, carry-ins, the landing) ....................... yes
  would it make sense without the cascade? (captures and carry-ins are cascade objects) ................ no
  a count used as the argument? (moves are recorded, never bounded; the index test compares times) ...... no
  a rate or density as the answer? (exceptions listed one by one) ....................................... no
  an instant family the cascade does not visit? (the grid is read at the bound, where the cascade starts) no
  "first isolation" used? ................................................................................ no
  another proof's architecture as the object? ............................................................ no

RUN (exact).  Per set: sigma, 7/sigma; the captures at the bound with their slots; every move with its length in R and
the readings it carried in, with the eighth-slot each held at the move's start; the push's extent; the index (P's clear
interval holding the landing, E201 v2).  Classes of first-interval landings: A no capture (landing at the bound); B one
separation, nothing carried in; C carry-ins (a chain).  Second-interval landings: where the push stood at 7/sigma.
Populations as E201: every set <= 24; the late fine band shapes; Case C samples (seeds 13 and 29).
"""
import sys, math, random, itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cd, E8, next_opening
from wave_incident_v1 import lonely_components
from e151_block_v1 import slow_part, trace


def eighth(x):
    """The eighth-slot (0..7) and its deviation of a position x (in laps)."""
    y = 8 * (x - math.floor(x))
    s = math.floor(y)
    return s, y - s


def study(S):
    S = tuple(sorted(S)); d0 = S[0]
    P = slow_part(S); Fp = [d for d in S if d not in P]
    sigma = F(P[-1], d0); Rend = F(7) / sigma
    ts, moves = trace(S)
    R = lambda t: 8 * d0 * t
    Iv = lonely_components(list(P), F(1, 8 * d0), ts + F(2, d0))
    idx = next((i for i, (a, b) in enumerate(Iv) if a <= ts <= b), None)
    caps = [(f, eighth(f * F(1, 8 * d0))) for f in S if cd(f * F(1, 8 * d0)) < E8]
    steps = []
    for i, (t, way, st, nx) in enumerate(moves):
        nxt_way = moves[i + 1][1] if i + 1 < len(moves) else ()
        carried = [(d, eighth(d * t), d > st[0]) for d in nxt_way]
        steps.append(dict(R0=R(t), dR=R(nx) - R(t), setter=st, way=way, carried=carried))
    extent = R(ts) - 1
    if idx == 0:
        cls = 'A' if not moves else ('B' if len(moves) == 1 else 'C')
    else:
        cls = None
    at_end = None
    if idx is not None and idx >= 1:
        inside = [s for s in steps if s['R0'] <= Rend]
        at_end = dict(n_inside=len(inside), way_at_end=[s['way'] for s in steps if s['R0'] <= Rend][-1:] if inside else [])
    return dict(S=S, P=tuple(P), sigma=sigma, Rend=Rend, idx=idx, cls=cls, caps=caps, steps=steps, extent=extent,
                check=(idx == 0) == (R(ts) <= Rend), at_end=at_end, nmoves=len(moves))


def chunk(first):
    return [study((first,) + rest) for rest in itertools.combinations(range(first + 1, 25), 6)]


def report(name, rows, w):
    w("\n== %s: %d sets ==" % (name, len(rows)))
    w("  CHECK index 0 <=> the landing is by R = 7/sigma (derived): %d violations" % sum(not r['check'] for r in rows))
    w("  index: %s" % dict(sorted(Counter(r['idx'] for r in rows).items(), key=lambda kv: (kv[0] is None, kv[0] or 0))))
    z = [r for r in rows if r['idx'] == 0]
    w("  first-interval landings by class (A no capture / B one separation / C carry-ins): %s" %
      dict(sorted(Counter(r['cls'] for r in z).items())))
    w("  captures at the bound, their eighth-slot and deviation class (slot 0, or slot 7): %s" %
      dict(Counter(s for r in rows for f, (s, dev) in r['caps'] if f not in r['P']).most_common()))
    car = [c for r in rows for s in r['steps'] for c in s['carried']]
    w("  carried in, by the eighth-slot held at the move's start: %s" % dict(Counter(c[1][0] for c in car).most_common()))
    w("  carried in, faster than the setter (bridge up) / not: %s" % dict(Counter(c[2] for c in car)))
    tight = sorted((r for r in z if r['extent'] > 0), key=lambda r: (r['Rend'] - 1 - r['extent']) / (r['Rend'] - 1) if r['Rend'] > 1 else 0)[:12]
    w("  first-interval landings closest to the interval end (push extent against 7/sigma - 1):")
    for r in tight:
        w("    %s P %s sigma %s extent %s of %s, moves %d" % (r['S'], r['P'], r['sigma'], r['extent'], r['Rend'] - 1, r['nmoves']))
    later = [r for r in rows if r['idx'] not in (0,)]
    w("  landings after the first interval: %d; sigma of their slow part: %s" %
      (len(later), dict(Counter(str(r['sigma']) for r in later).most_common(10))))
    for r in later[:25]:
        w("    %s P %s sigma %s (7/sigma %s) index %s moves %d; captures at the bound %s" %
          (r['S'], r['P'], r['sigma'], r['Rend'], r['idx'], r['nmoves'], [(f, s) for f, (s, dev) in r['caps']]))
        for s in r['steps'][:10]:
            w("        R %s +%s: in the slot %s, setter %s, carried in %s" %
              (s['R0'], s['dR'], s['way'], s['setter'], [(d, sl) for d, (sl, dv), up in s['carried']]))


if __name__ == '__main__':
    sys.path.insert(0, '.')
    from coverB_fine_v1 import late_shapes
    out = open('e202_index_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    rng = random.Random(13); cc1 = []
    while len(cc1) < 1000:
        T = tuple(sorted(rng.sample(range(1, 201), 7)))
        if T[-1] > 24 * T[0]:
            cc1.append(T)
    rng = random.Random(29); cc2 = []
    while len(cc2) < 1000:
        T = tuple(sorted(rng.sample(range(1, 5001), 7)))
        if T[-1] > 24 * T[0]:
            cc2.append(T)
    with Pool(8) as pool:
        report('every 7-set of readings in 1..24', [r for part in pool.map(chunk, range(1, 19)) for r in part], w)
        report('late fine band shapes', pool.map(study, late_shapes()), w)
        report('Case C, readings <= 200 (seed 13)', pool.map(study, cc1), w)
        report('Case C, readings <= 5,000 (seed 29)', pool.map(study, cc2), w)
    out.close()
    print(open('e202_index_v1.out').read()[len(__doc__):][:8000])
