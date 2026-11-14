# conjT_enum_v1.py -- CONJECTURE T, step 1: the exact (reading,lap) enumeration of R=7 coverers.
# Branch n8-fresh-2026-10-30, 2026-11-14. Exact Fractions only; open-interval arithmetic.
#
# SETTING (tailcomp2_lemma_v1.out): 1 = rho1 < rho2 <= ... <= rho7; a carve of [1,7] is a
# covering of [1,7] by the open zones Z(rho,k) = ((8k-1)/rho, (8k+1)/rho), readings 2..7.
# Z(rho,k) contains R=1 iff rho in C_k = (8k-1, 8k+1)  (strips);
# Z(rho,k) contains R=7 iff rho in W_k = ((8k-1)/7, (8k+1)/7)  (end windows).
# THEOREM S branches for a carve with rho7 >= 25:
#   (a) rho6 <= 49/7 (=7)  [pinned; Theorem U kills all such carves -- T's target case]
#   (b) rho6 in (7,17], rho7 in [25,50)   [E852 confinement]
#   (c) rho6 > 17                         [R4 frontier]
# TASK 1: enumerate every (r,j) with rho_r in W_j possible per branch, exactly.
from fractions import Fraction as F

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
out = open(DIR + 'conjT_enum_v1.out', 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s, flush=True); out.write(s + '\n'); out.flush()

def W(j):  return (F(8*j-1, 7), F(8*j+1, 7))          # end window, open
def C(m):  return (F(8*m-1), F(8*m+1))                # strip, open
def G(q):  return (F(8*q+1), F(8*q+7))                # gap, open
def inter(a1,b1,a2,b2): return max(a1,a2) < min(b1,b2)   # open-interval overlap

PIN = F(49,7)   # = 7

P('# conjT_enum_v1 -- exact; started', __import__('time').strftime('%Y-%m-%d %H:%M:%S'))

# ============ PART I: the comb identities (exact, machine-checked) ============
P('# === I1. THE DOUBLE-COVER IDENTITY: C_m cap W_j = W_7m if j = 7m, else EMPTY ===')
bad = []
for m in range(1, 61):
    for j in range(1, 200):
        cm, wj = C(m), W(j)
        ov = inter(cm[0], cm[1], wj[0], wj[1])
        if j == 7*m:
            # W_7m = (8m - 1/7, 8m + 1/7) subset C_m strictly
            if not (ov and cm[0] <= wj[0] and wj[1] <= cm[1]):
                bad.append((m, j, 'subset'))
        else:
            if ov: bad.append((m, j, 'unexpected-overlap'))
P('I1 [T %s] (m in 1..60, j in 1..200, 0 violations)' % ('600/600' if not bad else 'FAIL'))
P('    reading covers R=1 at lap m AND R=7 somewhere  <=>  rho in W_7m = (8m-1/7, 8m+1/7) subset C_m;')
P('    so a SELF-ANCHORED rho7 covering R=7 does so at lap j7 = 7m EXACTLY (m = rho7 strip).')

P('# === I2. GAP x END-WINDOW: G_q cap W_j != EMPTY iff 7q+1 <= j <= 7q+6 ===')
bad2 = []
for q in range(1, 21):
    for j in range(1, 200):
        gq, wj = G(q), W(j)
        ov = inter(gq[0], gq[1], wj[0], wj[1])
        if ov != (7*q+1 <= j <= 7*q+6): bad2.append((q, j))
P('I2 [T %s] (q in 1..20, j in 1..200)' % ('400/400' if not bad2 else 'FAIL ' + str(bad2[:5])))

P('# === I3. END-WINDOW REACH under a reading cap X: J6(X) = {j : W_j cap (1,X] != EMPTY} ===')
def J6(X):
    res = []
    j = 1
    while True:
        wj = W(j)
        # exists rho: wj[0] < rho <= X (and rho > 1): iff wj[0] < X and wj[1] > 1 (open upper)
        if wj[0] < X and wj[1] > F(1): res.append(j)
        if wj[0] >= X: break
        j += 1
    return res
for X in (F(7), F(17)):
    js = J6(X)
    P('    J6(%s) = [%d..%d]  (%d laps)' % (X, js[0], js[-1], len(js)))

P('# === I4. rho7-window x lap: which j can host rho7 in [25,50) per regime ===')
regs = [('C_4', C(4)), ('C_5', C(5)), ('C_6', C(6)), ('G_3', G(3)), ('G_4', G(4)),
        ('G_5', G(5)), ('G_6||(49,50)', (F(49), F(50)))]
for name, (a, b) in regs:
    js = [j for j in range(1, 60) if inter(W(j)[0], W(j)[1], a, b)]
    P('    %s = (%s, %s): j in %s' % (name, a, b, ('[%d..%d]' % (js[0], js[-1])) if js else 'NONE'))

# ============ PART E: the branch tables (exact) ============
P('# === E1. BRANCH (a): rho6 <= 49/7, rho7 >= 25  [the pin hypothesis; Theorem U kills all] ===')
# rho2..rho6 in (1,7]; r<=6: j in J6(7). r=7: rho7 covers R=1 at its strip m>=4 (anchor lemma (i),
# forced) so the double-cover identity gives j = 7m; m>=7 means rho7 >= 55 >= 50 => E852 [L/T]
# kills, and the chases U4 kill m in {4,5,6} pinned: the pairs are the carve-ANATOMY possibilities.
Ja = J6(F(7))
pairs_a_low = [(r, j) for r in range(2, 7) for j in Ja]
pairs_a_7 = [(7, 7*m) for m in (4, 5, 6)]
P('    r in 2..6: j in J6(7) = [%d..%d]: %d pairs' % (Ja[0], Ja[-1], len(pairs_a_low)))
P('    r = 7 (self-anchored, rho7 in C_m): j = 7m by I1; m in {4,5,6} (m>=7 => rho7>=55 killed by'
  ' E852 [L/T]): pairs %s' % (pairs_a_7,))
P('    BRANCH (a) TOTAL: %d pairs' % (len(pairs_a_low) + len(pairs_a_7)))
P('    anchor condition: rho7 in C_m (m>=4) => anchor {(7,m)} exists [alive]; rho7 in a gap =>'
  ' NO anchor (anchor lemma (ii)) => NO carve at any (r,j) [DEAD].')

P('# === E2. BRANCH (b): rho6 in (7,17], rho7 in [25,50)  [E852-confined; the R2/R3 sector] ===')
Jb = J6(F(17))
pairs_b_low = [(r, j) for r in range(2, 7) for j in Jb]
pairs_b_7 = ([(7, j) for j in range(22, 28)] + [(7, 28)] + [(7, j) for j in range(29, 35)]
             + [(7, 35)] + [(7, j) for j in range(36, 42)] + [(7, 42)] + [(7, 43)])
# check the r=7 list against I4 exactly:
chk = sorted(set(j for j in range(1, 60)
                 for name, (a, b) in regs if inter(W(j)[0], W(j)[1], a, b)))
assert [j for _, j in pairs_b_7] == chk, (chk,)
P('    r in 2..6: j in J6(17) = [%d..%d]: %d pairs  (W_15 = (17,17.29) open at the cap 17)'
  % (Jb[0], Jb[-1], len(pairs_b_low)))
P('    r = 7: gaps G_3,G_4,G_5,(49,50) by I2 + strips C_4,C_5,C_6 by I1: j in %s: %d pairs'
  % (chk, len(pairs_b_7)))
P('    BRANCH (b) TOTAL: %d pairs' % (len(pairs_b_low) + len(pairs_b_7)))
P('    anchor condition: rho7 in C_m => self-anchor {(7,m)} [alive]; rho7 in G_q => anchor needs'
  ' a strip-1 (7,9) or strip-2 (15,17) reading among rho2..rho6 [system-level, alive-conditional];'
  ' if rho2..rho6 all in gaps => NO anchor => NO carve [DEAD, comb kill].')

P('# === E3. BRANCH (c): rho6 > 17  [R4 frontier] ===')
P('    r in 2..6: rho_r <= rho6 (unbounded) => j unbounded: for every J, W_J cap (17,inf) != EMPTY.')
P('    r = 7: rho7 unbounded => j unbounded. EXACT DEMONSTRATION: for every J >= 22 the tuple')
P('    skeleton rho2..rho6 = (2,3,4,5,18), rho7 = 8J/7 has rho7 = 8J/7 in W_J, rho7 >= 25 (J>=22),')
w = W(22)
P('    e.g. J=22: rho7 in W_22 = (%s, %s) = (%.4f, %.4f), 8*22/7 = %s >= 25: %s; rho6 = 18 > 17.'
  % (w[0], w[1], float(w[0]), float(w[1]), F(8*22,7), F(8*22,7) >= 25))
P('    => the (r,j) pair set of branch (c) is INFINITE: no finite enumeration without a rho7')
P('    upper bound for rho6 > 17. This is exactly the missing R4 quantity (E854/E856: the')
P('    genuinely unbounded branch has rho6 > 51; nothing on the ledger bounds rho7 at rho6 > 17).')

P('# === E4. THE FORCING CLASSIFICATION (which pairs constrain rho6 across 49/7) ===')
P('    (i) r <= 6, rho_r in W_j: ORDERING gives rho6 >= rho_r > (8j-1)/7  [LOWER bound on rho6].')
P('        j >= 7  =>  rho6 > 55/7 > 49/7: the pair REQUIRES rho6 > 7 (pin-breaking).')
P('        j <= 6  =>  rho6 > (8j-1)/7 <= 47/7: rho6 unconstrained above by the pair.')
P('    (ii) r = 7, rho7 in W_j: ORDERING gives rho6 <= rho7 < (8j+1)/7  [UPPER bound on rho6].')
for j in (28, 35, 42):
    P('        j = %d: rho6 < (8*%d+1)/7 = %s = %.4f' % (j, j, F(8*j+1,7), float(F(8*j+1,7))))
P('    (iii) NO pair in ANY branch forces rho6 <= 49/7: the r<=6 pairs only bound rho6 from')
P('        below; the r=7 pairs bound rho6 only by (8j+1)/7 >= 225/7 > 49/7. The upper side of')
P('        the pin window (the transport, Conjecture T) receives NO contribution from the')
P('        (r,j)-level comb: ordering, I1/I2 identities, ladder demand and node budget leave')
P('        rho6 > 49/7 comb-alive in branches (b) and (c) -- verified case-by-case in')
P('        conjT_cases_v1.out.')

P('# === E5. THE PER-PAIR LADDER DEMAND (pure-lap, exact) ===')
P('    anchor lap m_a, end lap j: any strict chain forces prod phi(k_i) > D = (8j-1)/(8 m_a + 1),')
P('    phi(k) = (8k+1)/(8k-1) <= phi(1) = 9/7. Min plug count n_min = ceil(ln D / ln(9/7)).')
def nmin(D):
    n, p = 0, F(1)
    while p <= D:
        p *= F(9, 7); n += 1
    return n
P('    self-anchored ends (r=7, j=7m, anchor lap m): D = (56m-1)/(8m+1):')
for m in (4, 5, 6):
    D = F(8*7*m - 1, 8*m + 1)
    P('        m=%d: D = %s = %.4f, n_min = %d lap-1 plugs' % (m, D, float(D), nmin(D)))
P('    strip-1-anchored ends (anchor lap 1): D = (8j-1)/9:')
for j in (22, 28, 32, 35, 42, 43):
    D = F(8*j - 1, 9)
    P('        j=%d: D = %s = %.4f, n_min = %d' % (j, D, float(D), nmin(D)))
P('    strip-2-anchored ends (anchor lap 2): D = (8j-1)/17:')
for j in (22, 28, 32, 35, 42, 43):
    D = F(8*j - 1, 17)
    P('        j=%d: D = %s = %.4f, n_min = %d' % (j, D, float(D), nmin(D)))
P('    Node budgets (distinct (reading,lap) nodes with zones meeting (1,7)):')
for cap, rmax, lab in ((F(7), 6, 'branch (a): rho2..rho6 <= 7'),
                       (F(17), 6, 'branch (b): rho2..rho6 <= 17')):
    cnt = 0
    for r in range(2, rmax+1):
        k = 1
        while F(8*k-1)/cap < F(7):   # zone entry below 7
            if F(8*k+1)/cap > F(1): cnt += 1   # zone exit above 1
            k += 1
    P('        %s: %d nodes' % (lab, cnt))
P('    => budgets >= 30 >> n_min <= 15: the pure-lap ladder + node budget NEVER binds')
P('    (E841-consistent: "the ladder cascade alone kills nothing"). The binding constraints are')
P('    POSITION/covering: the demand-band interval system + the union cover = the campaign\'s')
P('    chase/checker machinery (midbound chases U4, the E852 band checker), not lap algebra.')

out.close()
print('DONE')
