"""Order 5 (threshold 1/5), every flank has three other runners. Exhaustive over every 5-subset of [1,V], every runner, every
flank e. For each flank, exactly:
  - shadowed: every opening (5k+1)/(5e) has a runner in the way (period e in k; integer test (d(5k+1) mod 5e) in [e, 4e]);
  - k*: the first clear opening (how late the flank's instant is);
  - the ratio denominators c_j = e/gcd(d_j, e) of the non-integer ratios (1 = integer ratio: never in the way unless 5 | rho);
  - the flank criterion sum  Sigma = sum over non-integer ratios of (2/5 + 1/c_j); the criterion says Sigma < 1 => not shadowed.
Reports the contingency of (criterion flags: Sigma >= 1) against (shadowed, late k* >= 2, early), the denominator signatures of
the shadowed and late flanks, and any violation of the criterion."""
import itertools, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
n = 5
def flank_data(e, others):
    M = n * e
    kstar = None
    for k in range(e):
        if all(e <= (d * (n * k + 1)) % M <= (n - 1) * e for d in others):
            kstar = k; break
    dens = tuple(sorted(e // __import__('math').gcd(d, e) for d in others))
    sigma = sum(F(2, n) + F(1, c) for c in dens if c > 1)
    dead = any((d // __import__('math').gcd(d, e)) % n == 0 and e // __import__('math').gcd(d, e) == 1 for d in others)
    return kstar, dens, sigma, dead
def job(args):
    V, v = args
    out = Counter(); sig_shadow = Counter(); sig_late = Counter(); viol = []
    for i in range(n):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        for e in sorted(set(ds)):
            others = [d for d in ds if d != e]
            kstar, dens, sigma, dead = flank_data(e, others)
            flagged = sigma >= 1
            state = 'shadowed' if kstar is None else ('late' if kstar >= 2 else 'early')
            out[(flagged, dead, state)] += 1
            if state == 'shadowed': sig_shadow[dens] += 1
            elif state == 'late': sig_late[dens] += 1
            if kstar is None and not flagged and not dead: viol.append((v, i, e, dens, str(sigma)))
    return out, sig_shadow, sig_late, viol
if __name__ == '__main__':
    V = 30
    tot = Counter(); SS = Counter(); SL = Counter(); VI = []
    with Pool() as pool:
        for out, ss, sl, vi in pool.imap_unordered(job, [(V, v) for v in itertools.combinations(range(1, V + 1), n)], chunksize=300):
            tot.update(out); SS.update(ss); SL.update(sl); VI += vi[:3]
    print(f'order 5, every 5-subset of [1,{V}], every runner, every flank: {sum(tot.values())} flanks')
    print('(criterion flags Sigma>=1, dead flank, state) -> count:')
    for k in sorted(tot, key=lambda k: -tot[k]): print(f'   {k}: {tot[k]}')
    print('criterion violations (shadowed while Sigma < 1, not dead):', len(VI), VI[:3])
    print('denominator signatures of shadowed flanks:', SS.most_common(10))
    print('denominator signatures of late flanks (k* >= 2):', SL.most_common(10))
