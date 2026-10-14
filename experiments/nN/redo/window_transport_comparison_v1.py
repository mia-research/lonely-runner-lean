"""Exact diagnostic, not a universal proof or Lean certificate.

Compare a two-exit predictor (without assuming its answer clear) with finite
lap-window coverage of whole AP-deformation paths. Cascade discovers labels;
49 affine inequalities independently establish each label's full parameter
interval. Uncovered intervals and exhausted discovery budgets are reported.
"""
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
import random


def clear(d, t):
    f = d*t - floor(d*t)
    return F(1, 8) <= f <= F(7, 8)


def step(ds, t):
    blocked = [d for d in ds if not clear(d, t)]
    return max(((ceil(d*t-F(1, 8))+F(1, 8))/d for d in blocked), default=t)


def oracle(ds):
    t = F(1, 8)/min(ds)
    for n in range(10000):
        u = step(ds, t)
        if u == t:
            return t, n
        t = u
    raise RuntimeError('discovery cap; no termination conclusion')


def interval(a, b, laps):
    """All s in [0,1] satisfying every window inequality, exactly."""
    lo, hi = F(0), F(1)
    for i in range(7):
        for j in range(7):
            A = (8*laps[j]+7)*a[i] - (8*laps[i]+1)*a[j]
            B = (8*laps[j]+7)*b[i] - (8*laps[i]+1)*b[j]
            if B > 0:
                lo = max(lo, -A/B)
            elif B < 0:
                hi = min(hi, -A/B)
            elif A < 0:
                return None
    return (lo, hi) if lo <= hi else None


def gaps(windows):
    cursor = F(0)
    out = []
    for lo, hi in sorted(windows):
        if lo > cursor:
            out.append((cursor, lo))
        cursor = max(cursor, hi)
    if cursor < 1:
        out.append((cursor, F(1)))
    return out


def path(target, subject):
    xs = [F(7)*(x-target[0])/(target[-1]-target[0]) for x in target]
    others = [j for j in range(8) if j != subject]
    a = [F(abs(j-subject)) for j in others]
    b = [abs(xs[j]-xs[subject])-d for j, d in zip(others, a)]
    windows = {}
    for event in (1, 3, 5, 7):
        labels = tuple(floor(d*F(event, 8)) for d in a)
        w = interval(a, b, labels)
        if w is not None:
            windows[labels] = w
    initial = not gaps(windows.values())
    for attempt in range(100):
        missing = gaps(windows.values())
        if not missing:
            break
        lo, hi = max(missing, key=lambda p: p[1]-p[0])
        s = (lo+hi)/2
        ds = [d+s*e for d, e in zip(a, b)]
        t, _ = oracle(ds)
        labels = tuple(floor(d*t) for d in ds)
        w = interval(a, b, labels)
        assert w is not None and w[0] <= s <= w[1]
        assert labels not in windows
        windows[labels] = w
    # Independent endpoint verification suffices because each slack is affine.
    for labels, (lo, hi) in windows.items():
        for s in (lo, hi):
            ds = [d+s*e for d, e in zip(a, b)]
            lower = max(F(8*k+1, 8)/d for k, d in zip(labels, ds))
            upper = min(F(8*k+7, 8)/d for k, d in zip(labels, ds))
            assert lower <= upper and all(clear(d, lower) for d in ds)
    return initial, windows, gaps(windows.values())


def run():
    rng = random.Random(177)
    named = [(0,1,2,3,4,5,6,7), (0,99,200,300,400,500,600,700),
             (0,1,50,105,106,136,189,199),
             (0,1,11,115,128,135,196,199),
             (0,1,12,65,92,128,175,196)]
    named += [(0,)+tuple(sorted(rng.sample(range(1, 201), 7))) for _ in range(3)]
    counts = Counter()
    for target in named:
        for subject in range(8):
            initial, windows, missing = path(target, subject)
            counts['paths'] += 1
            counts['AP_labels_cover'] += initial
            counts['full_path_covered'] += not missing
            print('PATH', target, 'subject', subject, 'AP_only', initial,
                  'windows', len(windows), 'uncovered', len(missing), flush=True)
    print('PATH_SUMMARY', dict(counts), flush=True)
    counts = Counter()
    failure = None
    population = [t[1:] for t in named]
    population += [tuple(sorted(rng.sample(range(1, 201), 7))) for _ in range(2000)]
    for ds in population:
        bound = F(1, 8*min(ds))
        first = step(ds, bound)
        if first == bound:
            counts['clear_at_bound'] += 1
            continue
        incoming = [d for d in ds if not clear(d, first)]
        if len(incoming) != 1:
            counts['not_single_incoming'] += 1
            continue
        second = step(ds, first)
        ok = all(clear(d, second) for d in ds)
        counts['single_incoming'] += 1
        counts['second_exit_clear' if ok else 'second_exit_blocked'] += 1
        if ok:
            assert oracle(ds)[0] == second
        elif failure is None:
            failure = (ds, str(first), incoming, str(second),
                       [d for d in ds if not clear(d, second)])
    print('TWO_EXIT_SUMMARY', dict(counts))
    print('FIRST_COUNTEREXAMPLE', failure)


if __name__ == '__main__':
    run()
