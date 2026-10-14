"""Can the depth-14 cap-reaching word be extended past the cap?

The beam that found it (`ladder_return_beam_w2500_v1.out`) stopped at depth 14 on reaching R = 7, so it
never asked whether a realisable word exists ABOVE the cap. That question is not cosmetic: the
finiteness framing (ORDER5_GROWTH_v2 section 4) takes the FIRST step at which R reaches the cap, so a
word that strictly exceeds it would mean the nearest runner returns and the framing needs rework.

This tries every legal one-move extension of the word and reports the realisable ones.
"""
import os, sys, time
os.environ.setdefault('ORDER', '8')
from fractions import Fraction as F

src = open(os.path.join(os.path.dirname(__file__), 'order_n_certificate_v1.py')).read().split("if __name__ ==")[0]
g = {'__name__': 'ext'}
exec(src, g)
constraints = g['constraints']; opt = g['opt']; NV = g['NV']; n = g['n']

WORD = [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (3, 2), (4, 2),
        (1, 4), (5, 2), (3, 3), (2, 4), (6, 2), (1, 6)]
S = 8
L = ((n - 1) * S - 1) // n
used = {x: q for x, q in WORD}

print(f"order {n}, ratio bound S = {S}, lap bound L = {L}, cap R < {n-1}")
print(f"extending the depth-{len(WORD)} cap word by one move\n")
t0 = time.time(); res = []; tried = 0
for nx in range(1, NV + 1):
    for nq in range(used.get(nx, 0) + 1, L + 1):
        tried += 1
        w = WORD + [(nx, nq)]
        cons = constraints(w)
        tau = opt(cons, NV, 'max', S, True)
        if tau is None or tau <= 0: continue
        m = opt(cons, nx - 1, 'min', S, False)
        if m is None or m <= 0: continue
        res.append((F(n * nq + 1) / m, (nx, nq), tau, m))
res.sort(reverse=True)
print(f"  candidate moves tried: {tried}   realisable: {len(res)}   ({time.time()-t0:.0f}s)")
for R, mv, tau, m in res[:10]:
    print(f"   move {mv}  tau {tau}  min u {m}  R = {R} = {float(R):.6f}"
          f"{'   ABOVE THE CAP' if R > n - 1 else ''}")
if not res:
    print("\n  No realisable extension: the word is TERMINAL.")
    print("  This matches the replay (`ladder_cap_word_replay_v1.out`), where the cascade reports")
    print(f"  LONELY after {len(WORD)} steps at every witness tested -- the cascade ends here, and the")
    print(f"  cap is approached as a terminal value, not crossed.")
