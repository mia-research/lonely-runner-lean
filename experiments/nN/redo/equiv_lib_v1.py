# Shared library for equiv_*_v1.py.  Exact Fractions.  Readings rho_1=1<...<rho_7 (units of smallest); R=8*d_min*t.
import sys, random, math
from fractions import Fraction as F
_here = __file__.rsplit('/', 1)[0] if '/' in __file__ else '.'
exec(open(_here + '/cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])      # pos, blocks, path
exec(open(_here + '/outcome_classes_v2.py').read().split('\nif __name__ ==')[0])      # outcome
def norm(rhos):
    s = sorted(rhos); m = s[0]; return [r / m for r in s]
def states(rhos):
    steps, Rend = path(rhos); return tuple([mv["R"] for mv in steps] + [Rend])
def full(rhos):
    """rhos any list of 7 positive Fractions (need not be sorted/normalised). Returns dict with states (normalised units), path (rank,lap), R, opener, closer."""
    n = norm(rhos); o = outcome(n); o['states'] = states(n); o['rho'] = n; return o
def clear_all(r, sts): return all(not blocks(R, r) for R in sts)
def q(x, d=1000): return F(round(x * d), d)
def gen(rnd):
    k = rnd.choice((0, 1, 2, 3, 4))
    if k == 0: xs = [q(math.exp(rnd.uniform(0, math.log(rnd.choice((9, 30, 100)))))) for _ in range(7)]
    elif k == 1:
        xs = [F(j) for j in range(1, 8)]
        for m in rnd.sample(range(7), rnd.choice((1, 2, 3))): xs[m] = max(F(11, 10), xs[m] + q(rnd.uniform(-1.5, 3.5)))
    elif k == 2: xs = [F(rnd.randint(1, 40)) for _ in range(7)]
    elif k == 3: xs = [F(rnd.randint(8, 400), rnd.randint(1, 12)) for _ in range(7)]
    else:
        b = q(rnd.uniform(1, 9)); xs = [F(1)] + [b + q(rnd.uniform(0, 1.2), 100) for _ in range(6)]
    xs = norm(xs)
    return xs if len(set(xs)) == 7 and xs[1] > 1 else gen(rnd)
def cx_key(rho): return (max(r.denominator for r in rho), sum(abs(r.numerator) for r in rho))
def fl(x): return float(x)
def fmt(rho): return "[" + ", ".join(str(r) for r in rho) + "]"
def pool(seed, n, move_frac=0.6):
    """n arrangements; about move_frac have at least one cascade move (not lonely at R=1)."""
    rnd = random.Random(seed); out = []; nm = 0
    while len(out) < n:
        a = gen(rnd); moved = len(states(a)) > 1
        if moved and nm < move_frac * n: out.append(a); nm += 1
        elif (not moved) and (len(out) - nm) < (1 - move_frac) * n: out.append(a)
    return out, rnd
def cmp(a, b):
    """what is preserved between two full() results: S states, P (rank,lap) path, L landing, O opener, C closer"""
    return dict(S=a['states'] == b['states'], P=a['path'] == b['path'], L=a['R'] == b['R'], O=a['opener'] == b['opener'], C=a['closer'] == b['closer'])
def entry_after(R, r):
    """smallest zone entry (8j-1)/r, j>=1, that is >= R ; returns (value, j)"""
    j = max(1, int(-(-(R * r + 1) // 8)))
    while 8 * j - 1 < R * r: j += 1
    while j > 1 and 8 * (j - 1) - 1 >= R * r: j -= 1
    return F(8 * j - 1) / r, j
def closer_id(rhos, R):
    """identity-labelled closer (index in the list given, j) and entry value"""
    best = None
    for i, r in enumerate(rhos):
        e, j = entry_after(R, r)
        if best is None or e < best[0]: best = (e, (i, j))
    return best[1], best[0]
def ident(rhos):
    """identity-labelled data on the list as given (no sorting): states, path (index,lap), landing, closer id"""
    steps, R = path(rhos); cid, e = closer_id(rhos, R)
    return dict(S=tuple([s['R'] for s in steps] + [R]), I=tuple((s['setter'], s['lap']) for s in steps), L=R,
                O=((steps[-1]['setter'], steps[-1]['lap']) if steps else None), C=cid, E=e)
def cmpi(a, b):
    return {k: a[k] == b[k] for k in ('S', 'I', 'L', 'O', 'C')}
