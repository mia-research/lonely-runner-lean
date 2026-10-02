"""E265/E266 (2026-10-02): why the slowest cluster flank clears; the 21 rank-1 exceptions through the cascade.  Design: log E265.
Reading: rho_j(u) = x_j u / e mod 8 = A_j + eps_j u (mod 8), x_j/e = A_j + eps_j; in the way iff rho_j in (-1, 1) mod 8."""
import sys, os, json, io, contextlib, random, math
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); os.chdir(HERE); sys.path.insert(0, '../band_cert_v1'); sys.path.insert(0, HERE)
import restricted_b_v1 as R, free_ranks_v1 as FR
from hole_C1_flanks_v1 import inway
from quantity_tests_v1 import cd, E8
from e151_block_v1 import trace


def run_us(c, e):
    k0 = -((-(e - c)) // (8 * c)); k1 = (7 * e - c) // (8 * c)
    return [8 * k + 1 for k in range(k0, k1 + 1)]


def flank_info(c, cl, e):
    """per opening the in-way set (indices into cl, excluding e), and exactness check of the line reading."""
    us = run_us(c, e); sets = []; bad = 0
    for u in us:
        s = set()
        for j, x in enumerate(cl):
            if x == e: continue
            rho = F(x * u, e) % 8
            A = round(F(x, e)); eps = F(x, e) - A
            if (A + eps * u) % 8 != rho: bad += 1
            if inway(x, u, e): s.add(j)
            assert (rho < 1 or rho > 7) == inway(x, u, e)
        sets.append(s)
    return us, sets, bad


def state(c, cl, e):
    us, sets, bad = flank_info(c, cl, e)
    first = next((i for i, s in enumerate(sets) if not s), None)
    if first is not None: return dict(state='free', t=F(us[first], 8 * e), idx=first, n=len(us), bad=bad)
    common = set.intersection(*sets)
    if common:
        j = min(common); x = cl[j]; A = round(F(x, e)); eps = F(x, e) - A
        return dict(state='alone', n=len(us), j=j, A=A, eps=eps, ratio=F(x, e), u_hi=us[-1], u_lo=us[0], bad=bad)
    return dict(state='handoff', n=len(us), sets=sets, us=us, bad=bad)


def landing(c, cl):
    """(rank 1..6 of the flank with the earliest first-clear opening, t); c in the way inside a run -> None."""
    best = None
    for i, e in enumerate(cl):
        st = state(c, cl, e)
        if st['state'] == 'free' and (best is None or st['t'] < best[1]): best = (i + 1, st['t'])
    return best


def lonely(S, t): return all(cd(d * t) >= E8 for d in S)


def mech_member(item):
    seed, mode, S = item; c = S[0]; cl = list(S[1:])
    out = []
    bad = 0
    for i, e in enumerate(cl):
        st = state(c, cl, e); bad += st['bad']
        row = dict(rank=i + 1, state=st['state'])
        if st['state'] == 'alone':
            row.update(A=st['A'], A8=st['A'] % 8, sign='+' if st['eps'] > 0 else '-', ratio=float(st['ratio']), eps_ulo=float(abs(st['eps']) * st['u_lo']), eps_span=float(abs(st['eps']) * (st['u_hi'] - st['u_lo'])))
        out.append(row)
    return seed, mode, out, bad


def rand_cluster(rnd):
    c = rnd.randrange(10**6, 10**7); span = rnd.choice((1.5, 2, 3, 5, 8, 12, 20, 40))
    lo = 25 * c
    cl = sorted(rnd.randrange(lo, int(lo * span)) for _ in range(6))
    return c, cl


def rand_job(seed):
    rnd = random.Random(seed); rows = []
    for _ in range(300):
        c, cl = rand_cluster(rnd)
        if len(set(cl)) < 6: continue
        for i, e in enumerate(cl):
            us = run_us(c, e)
            if any(inway(c, u, e) for u in us): continue
            st = state(c, cl, e)
            if st['state'] == 'alone':
                rows.append((i + 1, int(st['A'] % 8), '+' if st['eps'] > 0 else '-', float(st['ratio']), float(abs(st['eps']) * (st['u_hi'] - st['u_lo']))))
            else: rows.append((i + 1, st['state']))
    return rows


def shifts(item):
    seed, mode, S = item; c = S[0]; cl = list(S[1:]); e1, e2 = cl[0], cl[1]
    base_land = landing(c, cl); res = dict(S=S, seed=seed, mode=mode, base=base_land[0] if base_land else None, rows=[])
    for j in range(6):
        for d in (-0.25, -0.1, -0.05, -0.01, 0.01, 0.05, 0.1, 0.25):
            cl2 = list(cl); cl2[j] = cl[j] + int(round(d * e1))
            if len(set(cl2)) < 6 or min(cl2) <= 24 * c: continue
            cl2 = sorted(cl2)
            st1 = state(c, cl2, cl2[0])['state']
            L2 = landing(c, cl2)
            chk = ''
            if L2:
                S2 = tuple([c] + cl2); t = L2[1]
                if not lonely(S2, t): chk = 'not lonely'
                ts, _ = trace(S2)
                if ts != t: chk += ' cascade != earliest first-clear'
            res['rows'].append((j, d, st1, L2[0] if L2 else None, chk))
    # witness readings at e2 (the free flank for the exception), and the shadower at e2
    st1 = state(c, cl, e1); st2 = state(c, cl, e2)
    wit = None
    if st2['state'] == 'free':
        u = run_us(c, e2)[st2['idx']]
        wit = []
        for j, x in enumerate(cl):
            if x == e2: continue
            rho = F(x * u, e2) % 8
            wit.append((j + 1, float(rho), float(min(rho - 1, 7 - rho))))
    shd = []
    occ = set(st1['common']) if False else None
    if st1['state'] == 'alone':
        j = st1['j']; x = cl[j]; A2 = round(F(x, e2)); eps2 = F(x, e2) - A2
        eta = F(e2, e1) - 1
        shd.append(dict(j=j + 1, A1=int(st1['A']), eps1=float(st1['eps']), A2=int(A2), eps2=float(eps2), eta=float(eta), pred_eps2=float(F(x, e1) / (1 + eta) - A2)))
    elif st1['state'] == 'handoff':
        occs = Counter(j for s in st1['sets'] for j in s)
        for j, cnt in occs.most_common(6):
            x = cl[j]; A1 = round(F(x, e1)); eps1 = F(x, e1) - A1; A2 = round(F(x, e2)); eps2 = F(x, e2) - A2
            shd.append(dict(j=j + 1, openings=cnt, of=st1['n'], A1=int(A1), eps1=float(eps1), A2=int(A2), eps2=float(eps2)))
    res['wit'] = (u if st2['state'] == 'free' else None, wit); res['shd'] = shd; res['st1'] = st1['state']; res['st2'] = st2['state']
    return res


if __name__ == '__main__':
    M = json.load(open(R.NN + '/residual_members_C_list_v1.json'))
    items = [(118, m, tuple(S)) for m in 'AB' for S in M[m]]
    with Pool(10) as pool:
        for part in pool.map(FR.members, range(201, 211)): items += part
    json.dump([list(i) for i in items], open('members_5978_v1.json', 'w'))
    out = open('slow_flank_mech_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    with Pool(10) as pool:
        res = pool.map(mech_member, items, chunksize=40)
        w("members: %d; line reading rho = (A + eps u) mod 8 vs (x u/e) mod 8 mismatches over all openings: %d" % (len(res), sum(r[3] for r in res)))
        # 1. alone states by rank
        al = [(rank['rank'], rank) for _, _, out_, _ in res for rank in out_ if rank['state'] == 'alone']
        w("\n[1] single-walker shadows across the whole run, by cluster rank (members): %s" % dict(sorted(Counter(r for r, _ in al).items())))
        for rk in range(1, 7):
            X = [x for r, x in al if r == rk]
            if not X: continue
            w("   rank %d: %d; (A mod 8, sign eps): %s; min ratio x_j/e = %.4f; max |eps|*u_lo = %.3f; max |eps|*(u_hi-u_lo) = %.3f" % (
                rk, len(X), dict(Counter((x['A8'], x['sign']) for x in X)), min(x['ratio'] for x in X), max(x['eps_ulo'] for x in X), max(x['eps_span'] for x in X)))
        viol = [x for r, x in al if r == 1 and x['ratio'] <= 7]
        w("   READING 1 at rank 1 (alone => ratio > 7, A mod 8 in {0,1,7} with the block-keeping sign): ratio <= 7 violations: %d; (A mod 8, sign) outside the allowed set: %d" % (
            len(viol), sum(1 for r, x in al for _ in [0] if (x['A8'], x['sign']) not in ((0, '+'), (0, '-'), (1, '-'), (7, '+')))))
        # 2. random clusters
        rr = [r for part in pool.map(rand_job, range(40)) for r in part]
        w("\n[2] random clusters (c in [1e6,1e7), cluster in [25c, 25c*span), span from 1.5 to 40), flanks with c never in the way: %d" % len(rr))
        for rk in range(1, 7):
            a = [x for x in rr if x[0] == rk and len(x) == 5]; tot = sum(1 for x in rr if x[0] == rk)
            if tot: w("   rank %d: flanks %d; single-walker shadows %d; min ratio of the shadower %.4f; (A mod 8, sign): %s; max |eps|*(span) %.3f" % (
                rk, tot, len(a), min((x[3] for x in a), default=float('nan')), dict(Counter((x[1], x[2]) for x in a)), max((x[4] for x in a), default=0)))
        a1 = [x for x in rr if x[0] == 1 and len(x) == 5]
        w("   rank 1 violations of 'alone => ratio > 7': %d; outside allowed (A mod 8, sign): %d" % (sum(1 for x in a1 if x[3] <= 7), sum(1 for x in rr if len(x) == 5 and (x[1], x[2]) not in ((0, '+'), (0, '-'), (1, '-'), (7, '+')))))
        # 3. the 21
        exc = [it for it, r in zip(items, res) if r[2][0]['state'] != 'free']
        w("\n[3] rank-1 exceptions: %d" % len(exc))
        P = pool.map(shifts, exc)
    for r in P:
        c = r['S'][0]; cl = r['S'][1:]
        w("\nseed %d %s: base landing rank %s; rank-1 state %s; rank-2 state %s; x/x1 %s" % (r['seed'], r['mode'], r['base'], r['st1'], r['st2'], [round(x / cl[0], 3) for x in cl]))
        w("   shadower(s) at e1 and at e2: %s" % r['shd'])
        u, wit = r['wit']
        w("   rank-2 witness opening u = %s: readings (walker, rho, margin to block edge): %s" % (u, [(a, round(b, 3), round(m, 3)) for a, b, m in wit] if wit else None))
        fr = Counter(); lm = Counter(); chk = Counter()
        for j, d, st1, land, ck in r['rows']:
            if ck: chk[ck] += 1
            if st1 == 'free': fr[j + 1] += 1
            lm[(j + 1, land)] += 1
        tot = Counter(j + 1 for j, d, st1, land, ck in r['rows'])
        w("   shifts freeing rank 1, by shifted walker (of %s): %s; landing ranks by shifted walker: %s; CHECKS: %s" % (dict(tot), dict(fr), dict(sorted(lm.items(), key=lambda kv: (kv[0][0], str(kv[0][1])))), dict(chk) if chk else '0 failures'))
    out.close(); print(open('slow_flank_mech_v1.out').read()[len(__doc__):])
