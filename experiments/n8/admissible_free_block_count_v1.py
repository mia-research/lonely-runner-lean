# Of the residual-box subject pairs left after ratio/unblocked, first-lap and no-multiple (2,670 in E632): how many are a ONE-FREE reading or a BLOCK SPLIT (real forms, E633)?
# one-free: exists x in S with G = gcd(S \ {x}) and G does not divide x (best unit is G itself: a unit G/j is a harder test for x).
# block split: sorted S, split after index i (core = S[:i], block = S[i:], both nonempty): gcd(block) >= 28 * max(core) (best unit is the gcd).
import sys, math, collections
from fractions import Fraction as F
sys.argv = ['x']
exec(open('residual_swap_v1.py').read().split("\nif __name__ ==")[0])
def flags(S):
    S = sorted(set(S)); m = S[0]
    ratio = S[-1] <= 7 * m
    unblocked = all(m <= d % (8 * m) <= 7 * m for d in S)
    firstlap = any(all(e <= d * (8 * n + 1) <= 7 * e for d in S if d != e) for e in S for n in range(0, 7 * e // 8 + 1))
    g = 0
    for d in S: g = math.gcd(g, d)
    nomult = False
    for j in range(1, 9):
        ns = [F(j * d, g) for d in S]
        if any(n.denominator != 1 for n in ns): continue
        ns = [int(n) for n in ns]
        for q in range(2, 9):
            if all(n % q for n in ns): nomult = True
    onefree = False
    for x in S:
        G = 0
        for d in S:
            if d != x: G = math.gcd(G, d)
        if x % G != 0: onefree = True
    block = False
    for i in range(1, len(S)):
        G = 0
        for d in S[i:]: G = math.gcd(G, d)
        if G >= 28 * S[i - 1]: block = True
    return ratio, unblocked, firstlap, nomult, onefree, block
cnt = collections.Counter(); tot = 0
for dd, res in configs():
    sp = tuple(x + 1 for x in dd)
    isgrid = len({x % 8 for x in sp}) == 8
    for k in range(8):
        S = [abs(sp[j] - sp[k]) for j in range(8) if j != k]
        r, u, f, nm, of, bs = flags(S); tot += 1
        if isgrid or r or u or f or nm: continue
        cnt['remaining_2670'] += 1
        if of: cnt['onefree'] += 1
        if bs: cnt['blocksplit'] += 1
        if of or bs: cnt['either'] += 1
print('pairs', tot, dict(cnt))
