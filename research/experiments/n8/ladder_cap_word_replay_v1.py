"""Is the depth-14 cap-reaching word a real cascade, or an artefact of the relaxation?

The word LPs of `order_n_certificate_v1.py` impose only that each recorded setter is IN THE WAY at the
instant just before it sets, and that the instant advances. They drop two necessary conditions of the
actual cascade (ORDER5_CERTIFICATE_v2 section 1):

  (a) the setter is the one with the LATEST opening among all runners in the way;
  (b) the other runners are clear.

So an LP-realisable word need not be produced by the cascade. This script takes witness readings from
inside the word's own polytope and runs the actual cascade on them -- threshold 1/n, start at t = 1/n,
advance to the latest exit among the runners in the way -- and compares the word that comes out.

Three witnesses, because the question is not the same at each:
  * max-margin      -- the interior point, where the word is most comfortably realisable;
  * R-optimal(eps)  -- min final reading subject to tau >= eps, the corner where R -> 7 (the cap).
    This is the one that matters: the cap value lives at tau -> 0, so faithfulness AT the max-margin
    witness would not license the cap value.
"""
import os, sys
os.environ.setdefault('ORDER', '8')
from fractions import Fraction as F

src = open(os.path.join(os.path.dirname(__file__), 'order_n_certificate_v1.py')).read().split("if __name__ ==")[0]
g = {'__name__': 'replay'}
exec(src, g)
constraints = g['constraints']; simplex_min = g['simplex_min']; NV = g['NV']; n = g['n']
th = F(1, n)

WORD = [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (3, 2), (4, 2),
        (1, 4), (5, 2), (3, 3), (2, 4), (6, 2), (1, 6)]
S = 8

def solve(cons, obj, sense, with_tau):
    """Same LP as opt(), but returns the FULL solution vector, not just the objective."""
    nv = NV + 1 if with_tau else NV
    A = []; b = []
    for c in cons:
        A.append(list(c[:NV]) + ([c[NV]] if with_tau else []))
        b.append(c[NV + 1] - sum(c[:NV]))
    for i in range(NV):
        e = [F(0)] * nv; e[i] = F(1); A.append(e); b.append(F(S - 1))
    if with_tau:
        e = [F(0)] * nv; e[NV] = F(1); A.append(e); b.append(F(1))
    c = [F(0)] * nv
    c[obj] = F(-1) if sense == 'max' else F(1)
    r = simplex_min(A, b, c)
    if r is None or r == 'unbounded': return None
    x = r[1]
    u = [x[i] + 1 for i in range(NV)]                    # undo the u shift
    tau = x[NV] if with_tau else F(0)
    return u, tau

def cdist(z):
    """distance from z to the nearest integer, exactly"""
    f = z - int(z)
    if f < 0: f += 1
    return min(f, 1 - f)

def cascade(u, maxsteps=60):
    """The actual cascade. Readings: the nearest runner at 1, then u_1..u_NV.
    Zones are OPEN: in the way iff circDist(x*t) < 1/n. Start at t = 1/n (the nearest runner's exit).
    At each instant advance to the LATEST exit among the runners in the way."""
    readings = [F(1)] + list(u)                          # index 0 = nearest
    t = th
    word = []
    for _ in range(maxsteps):
        inway = []
        for i, x in enumerate(readings):
            p = x * t
            if cdist(p) < th:
                Q = int(p + F(1, 2)) if p >= 0 else 0    # nearest integer
                if abs(p - Q) >= th: Q = int(p) if p - int(p) < F(1,2) else int(p) + 1
                inway.append((i, Q, (F(Q) + th) / x))
        if not inway:
            return word, t, 'LONELY'
        i, Q, nt = max(inway, key=lambda r: r[2])
        word.append((i, Q))
        t = nt
    return word, t, 'DID NOT TERMINATE'

print(f"order {n}, ratio bound S = {S}, threshold 1/{n}, cap R < {n-1}")
print(f"target word (LP): {WORD}\n")

base = constraints(WORD)
x_last, Q_last = WORD[-1]
tests = [("max-margin", solve(base, NV, 'max', True))]
for eps in [F(1, 100), F(1, 1000), F(1, 10**6)]:
    cons = list(base) + [tuple([F(0)] * NV) + (F(-1), -eps)]
    tests.append((f"R-optimal, tau >= {eps}", solve(cons, x_last - 1, 'min', True)))

for name, sol in tests:
    if sol is None:
        print(f"--- {name}: LP infeasible"); continue
    u, tau = sol
    R = F(n * Q_last + 1) / u[x_last - 1]
    print(f"--- {name}")
    print(f"    readings u = {[str(v) for v in u]}")
    print(f"    tau = {tau}   R of the LP word = {R} = {float(R):.6f}")
    got, t_end, status = cascade(u)
    print(f"    cascade -> {status} after {len(got)} steps, t = {t_end} = {float(t_end):.6f}")
    print(f"    word produced: {got}")
    match = (got == WORD)
    print(f"    reproduces the LP word: {match}")
    if not match:
        k = next((i for i in range(min(len(got), len(WORD))) if got[i] != WORD[i]), min(len(got), len(WORD)))
        print(f"    first divergence at step {k+1}: cascade {got[k] if k < len(got) else '(ended)'}"
              f"  vs  LP {WORD[k] if k < len(WORD) else '(ended)'}")
    print()
