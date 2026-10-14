"""Cross-check the replay's cascade against the Lean definitions, transcribed verbatim.

`ladder_cap_word_replay_v1.py` implements the cascade from the prose rule ("advance to the latest exit
among the runners in the way"). That rule is stated in LADDER_BOUND_v1 section 1, but the authority is
the Lean artefact, and until now nothing checked the Python against it.

Transcribed from LonelyRunner/LonelyRunner/LRC/ (read 2026-09-17):

  Defs.lean:25        circDist x       = min (Int.fract x) (1 - Int.fract x)
  Iteration.lean:37   inWay n d t      <-> circDist (d * t) < (n : R)^-1
  Iteration.lean:39   nextOpening n d t = (ceil (d * t - (n : R)^-1) + (n : R)^-1) / d
  Iteration.lean:41   Lonely n ds s    <-> for all d in ds, (n : R)^-1 <= circDist (d * s)
  Iteration.lean:44   move n ds t      = ds.fold max t (fun d => if inWay n d t then nextOpening n d t else t)

Note the two conventions that decide boundary cases, and that they point opposite ways:
`inWay` is STRICT (`<`), `Lonely` is INCLUSIVE (`<=`). A runner exactly at distance 1/n is clear.

Lean's `move` returns only the new time; it does not name a setter. The word is built here by recording
the argmax, and ties are reported rather than silently broken -- a tie would make the word ambiguous
without changing the trajectory.

Termination follows Lean's `lonely_of_fixed`: a fixed point of `move` is a lonely instant.
"""
import os, sys
from fractions import Fraction as F

src = open(os.path.join(os.path.dirname(__file__), 'order_n_certificate_v1.py')).read()
os.environ.setdefault('ORDER', '8')

rep = open(os.path.join(os.path.dirname(__file__), 'ladder_cap_word_replay_v1.py')).read()
rep_head = rep.split('print(f"order {n}')[0]
g = {'__name__': 'xcheck', '__file__': os.path.join(os.path.dirname(__file__), 'ladder_cap_word_replay_v1.py')}
exec(rep_head, g)
solve = g['solve']; cascade_prose = g['cascade']; constraints = g['constraints']
NV = g['NV']; n = g['n']; WORD = g['WORD']; S = g['S']
INV_N = F(1, n)

# ---- Lean definitions, verbatim ------------------------------------------------
def fract(x):           return x - (x.numerator // x.denominator)
def circDist(x):        return min(fract(x), 1 - fract(x))
def inWay(d, t):        return circDist(d * t) < INV_N
def ceil_(x):           return -((-x.numerator) // x.denominator)
def nextOpening(d, t):  return (F(ceil_(d * t - INV_N)) + INV_N) / d
def Lonely(ds, s):      return all(INV_N <= circDist(d * s) for d in ds)
def move(ds, t):
    acc = t
    for d in ds:
        acc = max(acc, nextOpening(d, t) if inWay(d, t) else t)
    return acc

def cascade_lean(ds, maxsteps=60):
    """Iterate `move` to a fixed point, recording the argmax as the setter at each step."""
    t = INV_N; word = []; ties = []
    for _ in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t:
            return word, t, ('LONELY' if Lonely(ds, t) else 'FIXED BUT NOT LONELY'), ties
        setters = [i for i, d in enumerate(ds) if inWay(d, t) and nextOpening(d, t) == t2]
        if len(setters) > 1: ties.append((len(word) + 1, setters))
        i = setters[0]
        Q = ceil_(ds[i] * t - INV_N)
        word.append((i, Q))
        t = t2
    return word, t, 'DID NOT TERMINATE', ties

print(f"order {n}, threshold 1/{n}, ratio bound S = {S}")
print(f"cross-check: prose-rule cascade (replay_v1) vs Lean definitions transcribed verbatim\n")

base = constraints(WORD)
x_last, Q_last = WORD[-1]
cases = [("max-margin", solve(base, NV, 'max', True))]
for eps in [F(1, 100), F(1, 1000), F(1, 10**6)]:
    cons = list(base) + [tuple([F(0)] * NV) + (F(-1), -eps)]
    cases.append((f"R-optimal, tau >= {eps}", solve(cons, x_last - 1, 'min', True)))

allok = True
for name, sol in cases:
    u, tau = sol
    ds = [F(1)] + list(u)                       # index 0 = the nearest runner, reading 1
    R = F(n * Q_last + 1) / u[x_last - 1]
    w_p, t_p, s_p = cascade_prose(u)
    w_l, t_l, s_l, ties = cascade_lean(ds)
    same = (w_p == w_l and t_p == t_l)
    ok = same and w_l == WORD
    allok &= ok
    print(f"--- {name}   (tau = {tau}, R = {float(R):.6f})")
    print(f"    prose rule : {s_p:>8}, {len(w_p):2} steps, t = {t_p}")
    print(f"    Lean defs  : {s_l:>8}, {len(w_l):2} steps, t = {t_l}")
    print(f"    the two agree on word and final instant : {same}")
    print(f"    Lean-definition word reproduces the LP word : {w_l == WORD}")
    print(f"    setter ties (would make the word ambiguous) : {ties if ties else 'none'}")
    if not same:
        k = next((i for i in range(min(len(w_p), len(w_l))) if w_p[i] != w_l[i]), None)
        print(f"    FIRST DIVERGENCE at step {k+1 if k is not None else 'length'}:"
              f" prose {w_p[k] if k is not None else len(w_p)} vs Lean {w_l[k] if k is not None else len(w_l)}")
    print()
print(f"all cases agree, and reproduce the LP word: {allok}")
