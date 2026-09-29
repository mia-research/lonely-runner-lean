"""Exact checks of sufficient overlap budgets, NOT a coverage proof."""
from fractions import Fraction as F


def slack(d, t):
    return F((d*t-F(1, 8)).__floor__()) + F(7, 8) - d*t


def opening(d, t):
    assert slack(d, t) < 0
    return (F((d*t+F(1, 2)).__floor__())+F(1, 8))/d


def overlap_witness(outs, t):
    """Forward-exit construction used in the one/two-outsider Lean proof."""
    if not outs:
        return t
    a = outs[0]
    if len(outs) == 1:
        return opening(a, t) if slack(a, t) < 0 else t
    b = outs[1]
    if slack(a, t) < 0:
        t = opening(a, t)
    elif slack(b, t) < 0:
        t = opening(b, t)
        if slack(a, t) < 0:
            t = opening(a, t)
    if slack(b, t) < 0:
        t = opening(b, t)
    assert slack(a, t) >= 0 and slack(b, t) >= 0
    return t


def check(v, cap=300):
    assert min(v) > 0 and len(set(v)) == len(v)
    t = 1/(8*min(v))
    matches = []
    persistent = 0
    for step in range(cap):
        R = [slack(d, t) for d in v]
        active = [i for i, r in enumerate(R) if r < 0]
        if not active:
            return step, matches, persistent
        T = max(opening(v[i], t) for i in active)
        setters = [v[i] for i in active if opening(v[i], t) == T]
        for i in active:
            if slack(v[i], T) < 0:
                persistent += 1
                assert all(v[i] > 3*b for b in setters)
        # Every change in the protected set occurs at one of these D values.
        # Larger D only shortens the available interval until the next change.
        Ds = {v[i] for i in active} | {F(3, 4)*d/r for d, r in zip(v, R) if r > 0}
        valid = []
        for D in Ds:
            U = t+F(3, 4)/D
            outsiders = sorted(d for d, r in zip(v, R)
                               if not ((r < 0 and d <= D) or d*F(3, 4)/D <= r))
            if len(outsiders) > 2:
                continue
            wait = (F(0) if not outsiders else F(1, 4)/outsiders[0])
            if len(outsiders) == 2:
                wait += F(1, 2)/outsiders[1]
            if T+wait <= U:
                s = overlap_witness(outsiders, T)
                assert T <= s <= U and all(slack(d, s) >= 0 for d in v)
                valid.append(len(outsiders))
        if valid:
            matches.append((step, min(valid)))
        t = T
    raise RuntimeError("step cap: this trace is unresolved")


if __name__ == "__main__":
    seeds = {
        "late_a": ["1", "2.3509", "3.2412", "4.1886", "5.2223", "5.7871", "7.4378"],
        "late_b": ["1", "2.5302", "3.2218", "4.1563", "4.531", "5.6544", "7.0302"],
        "review": [".99", "2", "3", "4", "5", "6", "7"],
        "far_outsider": ["1", "1.2", "1.4", "1.6", "1.8", "2", "104"],
    }
    for name, values in seeds.items():
        steps, matches, persistent = check(list(map(F, values)))
        print(f"{name}: moves={steps}, sufficient_budget_steps={matches}, "
              f"persistent_old_blocks={persistent}")
    assert overlap_witness([F(1), F(8)], F(7, 8)) == F(73, 64)
    assert check(list(map(F, seeds["review"])))[1] == []
    print("All exact checks passed. The review case is NOT covered by these width budgets.")
