# conjT_cases_v1.py -- CONJECTURE T, step 2: per-(r,j) constraint derivation (exact).
# For every enumerated R=7-coverer pair (r,j) of branches (a),(b): the exact rho6-window from
# ordering, the anchor requirement/availability, the chain-start (front-sliver) feasibility,
# the ladder demand vs the exact max phi-product over the node budget, spanner existence,
# and the verdict: PAIR-DEAD (comb kill, reason named) or PAIR-ALIVE (comb), with the
# flag whether the pair forces/allows rho6 > 49/7. Exact Fractions; open intervals.
from fractions import Fraction as F
import itertools, math

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
out = open(DIR + 'conjT_cases_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

def W(j):  return (F(8*j-1, 7), F(8*j+1, 7))
def C(m):  return (F(8*m-1), F(8*m+1))
def G(q):  return (F(8*q+1), F(8*q+7))
def inter(a1,b1,a2,b2): return max(a1,a2) < min(b1,b2)

PIN = F(49, 7)
PHI = lambda k: F(8*k+1, 8*k-1)

P('# conjT_cases_v1 -- exact; started', __import__('time').strftime('%Y-%m-%d %H:%M:%S'))

# exact max phi-product over the node budget of a branch (SOUND over-approximation of any
# node-simple chain's ladder product): nodes = (reading, lap), zone meeting (1,7);
# per lap k, n_k = number of readings able to host a lap-k zone inside (1,7) under the caps.
def max_phi_product(X6, X7):
    prod = F(1); nodes = 0; k = 1
    while True:
        n_k = 0
        # rho2..rho6 (5 readings, cap X6): exists rho <= X6 with zone-lap-k meeting (1,7)
        # iff max(1, (8k-1)/7) < min(X6, 8k+1)
        if max(F(1), F(8*k-1, 7)) < min(X6, F(8*k+1)): n_k += 5
        # rho7 (cap X7):
        if max(F(1), F(8*k-1, 7)) < min(X7, F(8*k+1)): n_k += 1
        if F(8*k-1, 7) >= X7 and F(8*k-1, 7) >= X6: break
        if n_k: prod *= PHI(k) ** n_k; nodes += n_k
        k += 1
    return prod, nodes

# the front-sliver band (F1, midbound2_mono): after the anchor (rho_a, m_a) the next chain zone
# can be a lap-1 zone of rho_b iff rho_b in [7 rho_a/(8 m_a + 1), 9 rho_a/(8 m_a + 1)) --
# nonempty under a reading cap X iff 7 rho_a/(8 m_a + 1) < X.
# rho_a lower edge = 8 m_a - 1 (strip) => sliver exists iff 7(8 m_a - 1)/(8 m_a + 1) < X.
def sliver_ok(m_a, X): return F(7*(8*m_a-1), 8*m_a+1) < X

# spanner band (E839 L3 generalized): a single zone (p,k) spanning (exit(anchor), entry(end)):
# rho_p > (8k-1) rho_r/(8j-1)  and  rho_p < (8k+1) rho_a/(8 m_a + 1);
# nonempty for SOME rho_a <= rho_r under caps: use rho_a as small as allowed, rho_r as small as
# allowed: exact check with the extreme reading values available in the branch.
# Here: anchor reading rho_a in C_{m_a} (lower edge 8 m_a - 1); end reading rho_r in W_j
# (lower edge (8j-1)/7). Band nonempty iff (8k-1)*(8j... we test with rho_a = 8 m_a - 1 (min),
# rho_r = (8j-1)/7 (min): strictness preserved by openness at the minimum edges? We test
# existence: take rho_a -> 8 m_a - 1^+, rho_r -> (8j-1)/7^+: band lo = (8k-1) rho_r/(8j-1) ->
# (8k-1)/7; band hi = (8k+1) rho_a/(8 m_a+1) -> (8k+1)(8 m_a-1)/(8 m_a+1). Nonempty iff
# (8k-1)/7 < (8k+1)(8 m_a - 1)/(8 m_a + 1) AND the band meets a reading <= cap.
def spanner_ok(m_a, j, X):
    lo = F(8*1-1, 7)   # best (smallest) spanner: k = 1 minimizes lo; check k = 1..: any k with band < cap
    for k in range(1, 40):
        lo_k = F(8*k-1, 7)
        hi_k = F((8*k+1)*(8*m_a-1), 8*m_a+1)
        if lo_k < hi_k and lo_k < X and hi_k > F(1):
            return True, k
        if lo_k >= X: break
    return False, None

def nmin(D):
    n, p = 0, F(1)
    while p <= D: p *= F(9,7); n += 1
    return n

REGS = [('C_4', 'strip', C(4), 4), ('C_5', 'strip', C(5), 5), ('C_6', 'strip', C(6), 6),
        ('G_3', 'gap', G(3), 3), ('G_4', 'gap', G(4), 4), ('G_5', 'gap', G(5), 5),
        ('(49,50)', 'gap', (F(49), F(50)), 6)]

BRANCHES = [
    ('(a) rho6 <= 49/7, rho7 >= 25 [pin hypothesis; Theorem U kills all pinned carves rho7>=25]',
     F(7), 'a'),
    ('(b) rho6 in (7,17], rho7 in [25,50) [E852-confined = the R2/R3 sector]', F(17), 'b'),
]

for bname, X6, btag in BRANCHES:
    P('# ' + '='*76)
    P('# BRANCH %s' % bname)
    P('# ' + '='*76)
    X7 = F(49) if btag == 'a' else F(50)
    maxprod, nnodes = max_phi_product(X6, X7)
    P('  node budget: %d (reading,lap) nodes (caps: rho2..rho6 <= %s, rho7 <= %s); exact max'
      % (nnodes, X6, X7))
    P('  phi-product over ALL of them (sound over-approx of any chain ladder) = %s ~= %.4f'
      % (maxprod, float(maxprod)))
    for rname, rkind, rwin, q in REGS:
        # rho7 laps (end coverer (7,j)) possible in this regime:
        if rkind == 'strip':
            j7s = [7*q]
        else:
            j7s = [j for j in range(1, 60) if inter(W(j)[0], W(j)[1], rwin[0], rwin[1])]
        # anchor availability:
        if btag == 'a':
            if rkind == 'gap':
                anch = []          # anchor lemma (ii): readings <= 7 anchor nothing; rho7 in gap
            else:
                anch = [(7, q)]    # forced self-anchor
        else:
            anch = []
            if rkind == 'strip': anch.append((7, q))
            # strip-1/strip-2 readings among rho2..rho6 possible (rho6 > 7):
            anch += [(6, 1), (6, 2)]   # some lower-indexed reading in (7,9) or (15,17)
        P('  -- rho7 regime %s = (%s, %s), %s: end laps for (7,j): %s | anchors: %s'
          % (rname, rwin[0], rwin[1], rkind, j7s, anch or 'NONE'))
        if not anch:
            P('     => NO anchor for ANY pair: NO CARVE (comb kill at every (r,j)). '
              '[anchor lemma (ii): the covering chain has no first zone]')
            continue
        rows = []
        # end coverers among rho2..rho6: j in J6(X6)
        js_low = [j for j in range(1, 60) if W(j)[0] < X6]
        # (7, j) end coverers:
        for j in j7s:
            rows.append((7, j))
        for j in js_low:
            for r in range(2, 7):
                rows.append((r, j))
        for (r, j) in sorted(rows):
            # ordering window for rho6:
            if r <= 6:
                lo6 = W(j)[0]
                w6 = (lo6, X6 if lo6 < X6 else None)
            else:
                w6 = (F(7) if btag == 'b' else F(1), min(X6, W(j)[1]))
                if btag == 'a': w6 = (F(1), min(X6, W(j)[1]))
            ok6 = w6[1] is not None and w6[0] < w6[1]
            pin_possible = ok6 and (w6[1] > PIN)   # rho6 > 49/7 admits comb-feasible values
            # PAIR-forced (ordering implies it): r <= 6 and the window's lower edge >= 49/7.
            # (r = 7 rows sit on the branch box's lower edge 7 in branch (b): branch-forced,
            #  not pair-forced -- the pair itself only gives the UPPER bound (8j+1)/7.)
            pin_forced  = ok6 and r <= 6 and w6[0] >= PIN
            # ladder demand per available anchor lap:
            ladds = []
            for (ar, al) in anch:
                if ar == 7 and rkind == 'strip':
                    D = F(8*j-1, 8*al+1)
                else:
                    D = F(8*j-1, 8*al+1)
                ladds.append((al, D, nmin(D)))
            # chain-start sliver per anchor lap (anchor reading in a strip / self):
            sliv = {al: sliver_ok(al, X6) for (ar, al) in anch}
            # spanner existence per anchor lap:
            span = {al: spanner_ok(al, j, X6)[0:2] for (ar, al) in anch}
            dmax = max(D for _, D, _ in ladds)
            ladder_ok = dmax < maxprod
            # verdict:
            if not ok6:
                verd = 'PAIR-DEAD (rho6-window empty under ordering+branch box)'
            elif not ladder_ok:
                verd = 'PAIR-DEAD (ladder demand exceeds max phi-product)'
            else:
                verd = 'PAIR-ALIVE (comb)'
            P('   (%d,%2d) rho6win=(%s, %s) %s | pin>7 %s%s | anchors %s | Dmax=%s=%.3f n_min=%s'
              ' | sliver %s | spanner %s | %s'
              % (r, j, w6[0], w6[1], 'OK' if ok6 else 'EMPTY',
                 'YES' if pin_possible else 'no',
                 ' [FORCED rho6>7]' if pin_forced else '',
                 anch, dmax, float(dmax), [n for _,_,n in ladds],
                 {k: v for k, v in sliv.items()}, {k: v for k, v in span.items()}, verd))
        P('')

P('# === SUMMARY OF THE PER-CASE DERIVATION ===')
P('(1) Branch (a): every rho7-in-gap (r,j) is DEAD at comb level (no anchor). Every')
P('    rho7-in-strip pair is ALIVE at comb level with the forced self-anchor; Theorem U')
P('    (chases U4 + E852 U5) kills all of them on the COVERING side -- branch (a) contains')
P('    no carves with rho7 >= 25, so the case-(a) anatomy is vacuous above 25: branch (a)')
P('    survives only as the HYPOTHESIS of the transport, not as a carve locus.')
P('(2) Branch (b): every pair is ALIVE at comb level (rho6-window nonempty above 49/7, ladder')
P('    under budget, sliver and spanner available). The comb kills only the anchor-less')
P('    sub-systems (rho2..rho6 all in gaps with rho7 in a gap). The pairs (r<=6, j in 7..14)')
P('    FORCE rho6 > 55/7; all other pairs leave rho6 > 49/7 free. So the exact comb-alive')
P('    "rho6 > 49/7 possible" case set = ALL of branch (b): the kill must come from the')
P('    covering side -- K2-nesting over gap columns (R2, exhaustive statement OWED at level 7)')
P('    and the de-pinned chases on C_4..C_6 (R3, never run unpinned).')
P('(3) Branch (c): pair set infinite (no rho7 bound); comb constraints cannot even enumerate.')
P('(4) VERDICT PREVIEW: the (r,j)-level comb arithmetic (ordering + identities I1/I2 + ladder')
P('    + node budget + sliver/spanner) NEVER forces rho6 <= 49/7 in any pair of any branch.')
P('    Conjecture T is NOT decidable at this level: its upper side is exactly as hard as the')
P('    covering-side instruments. See conjT_verdict_v1.out.')
out.close()
print('DONE')
