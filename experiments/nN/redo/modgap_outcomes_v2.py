"""modgap_outcomes_v2 (2026-10-06): the relation between the readings' residues mod q and the cascade's outcomes, on a large exact sample.
v2 (replaces v1, which stays): (a) the carrier is frac(q t*) = rho_q (v1 required K_q = 0 and found none); (b) only sets with at least one multiple of 8
(for d_min = 1 the cascade stops at t = 1/8 exactly when there is none, a fact Z_8 encodes by definition); features added: C_8 = (which readings are
multiples of 8, residues mod 8 of their cofactors d/8 in size order, multiset of residues mod 8 of the non-multiples), W_8 = (Z_8, multiset of residues
mod 8 of the non-multiples) and G_8 = (Z_8, residues mod 8 of the cofactors).  The question: what do residues add beyond Z_8?
Population: N_SAMPLE = 300,000 seeded random 7-subsets of [1, 64] that contain 1 (d_min = 1; the cascade then starts at t = 1/8) with gcd 1; each
reading set is run through the exact cascade.  (Seed 20261006; rule 14: the cascade is deterministic, the sample is the only random element.)
Exact step form [P]: from t = (8k+1)/(8e) a blocked reading d (||d t|| < 1/8) with signed gap s_d = d t - round(d t) moves the instant to
(8 round(d t) + 1)/(8 d) = t + (1/8 - s_d)/d; the next state is the largest such.  The gap s_d is the residue d(8k+1) mod 8e read as a position.
Outcomes per set: O_len = number of cascade moves (capped 5); O_rank = rank (by size) of the opener of the landing (first listed if several);
O_cls = class of the opener mod 8 in {m (multiple of 8), o (odd), t (2 mod 4), f (4 mod 8)}; O_K = floor(8 t*) (capped 3);
O_carr = whether some q in [2, 16] is a carrier (t* = rho_q/q, multiples of q alone).
Features per q: Z_q = which readings (by rank) are divisible by q; R_q = the multiset of residues mod q; Ro_q = residues mod q in size order.
Held-out test: train on one half, predict the other half by the majority outcome of the feature value in the training half; unseen feature values
fall back to the overall majority.  Reported: accuracy on the held-out half, the baseline (overall majority), a shuffled-label control (outcomes
permuted within the training half), and the share of held-out sets whose feature value was seen.
[PROVISIONAL: counting tool; supports: the reading of which moduli the outcomes depend on -- not a proof step]."""
import random, collections, sys, itertools
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd, floor
from functools import reduce
from modgap_lib_v1 import cascade, cascade_path, openers, typ8
N = 300000; rnd = random.Random(20261006)
rows = []
while len(rows) < N:
    S = tuple(sorted([1] + rnd.sample(range(2, 65), 6)))
    path = cascade_path(S); t = path[-1][0]; op = openers(S, t)
    if not op:   # lonely at the first instant t = 1/8: opener is the instant itself, no opener reading
        opener = None
    else: opener = op[0]
    mv = len(path) - 1
    carr = False
    for q in range(2, 17):
        M = [d // q for d in S if d % q == 0]
        if M and (q * t) % 1 == cascade(M): carr = True; break
    if not any(d % 8 == 0 for d in S): continue
    rows.append((S, mv, S.index(opener) if opener else -1, typ8(opener) if opener else 'L', floor(8 * t), carr))
O = {'O_len': lambda r: min(r[1], 5), 'O_rank': lambda r: r[2], 'O_cls': lambda r: r[3], 'O_carr': lambda r: r[5]}
FEAT = {}
for q in (2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16):
    FEAT['Z_%d' % q] = (lambda q: lambda S: tuple(d % q == 0 for d in S))(q)
    FEAT['R_%d' % q] = (lambda q: lambda S: tuple(sorted(d % q for d in S)))(q)
    FEAT['Ro_%d' % q] = (lambda q: lambda S: tuple(d % q for d in S))(q)
FEAT['W_8'] = lambda S: (tuple(d % 8 == 0 for d in S), tuple(sorted(d % 8 for d in S if d % 8)))
FEAT['G_8'] = lambda S: (tuple(d % 8 == 0 for d in S), tuple((d // 8) % 8 for d in S if d % 8 == 0))
FEAT['C_8'] = lambda S: (tuple(d % 8 == 0 for d in S), tuple((d // 8) % 8 for d in S if d % 8 == 0), tuple(sorted(d % 8 for d in S if d % 8)))
N = len(rows); half = N // 2
out = open('modgap_outcomes_v2.out', 'w'); out.write(__doc__ + "\n")
for oname, of in O.items():
    y = [of(r) for r in rows]
    cnt = collections.Counter(y[:half]); base_lab = cnt.most_common(1)[0][0]
    base = sum(1 for v in y[half:] if v == base_lab)
    out.write("\n==== outcome %s: values %s; baseline (majority of training half = %r) correct on %d of %d\n" % (oname, dict(sorted(collections.Counter(y).items(), key=str)), base_lab, base, N - half))
    ysh = y[:half][:]; random.Random(7).shuffle(ysh)
    res = []
    for fname, ff in FEAT.items():
        feats = [ff(r[0]) for r in rows]
        for lab, ys in (('real', y[:half]), ('shuffled', ysh)):
            table = collections.defaultdict(collections.Counter)
            for fv, v in zip(feats[:half], ys): table[fv][v] += 1
            ok = seen = 0
            for fv, v in zip(feats[half:], y[half:]):
                if fv in table: seen += 1; pred = table[fv].most_common(1)[0][0]
                else: pred = base_lab
                ok += (pred == v)
            if lab == 'real': r_ok, r_seen = ok, seen
            else: s_ok = ok
        res.append((r_ok, fname, r_seen, s_ok))
    for r_ok, fname, r_seen, s_ok in sorted(res, reverse=True)[:14]:
        out.write("  %-8s held-out correct %6d (baseline %6d, shuffled %6d); feature value seen in training for %6d of %d\n" % (fname, r_ok, base, s_ok, r_seen, N - half))
out.close(); print(open('modgap_outcomes_v2.out').read()[len(__doc__):])
