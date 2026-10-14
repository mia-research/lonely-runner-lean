#!/usr/bin/env python3
"""Grid plus deviation: the normal form of an arbitrary arrangement, and what the cascade does with it (task AW).

Rules: 1, 5, 6, 7, 13, 15, 16, 18, 21.   Exact only (integers, Fractions, Q(sqrt 2) pairs of Fractions); no floats.
No pre-registration, no imports of other frameworks' obligations.  Every cascade loop has a move limit.

Objects (all in the framework's own terms).
  D = {d_1 < ... < d_7} positive, m = d_min = d_1, rho_j = d_j / m, gate coordinate R = 8 m t.
  idx_j = nearest integer to rho_j (tie rho = k + 1/2: rounded UP, so e = -1/2; the other rule is tested in section 9),
  e_j = rho_j - idx_j.   res_j = idx_j mod 8, quo_j = floor(idx_j / 8), sgn_j = sign(e_j).
  Runner j is clear at R iff (idx_j R + e_j R) mod 8 lies in [1,7]   (Fresh/RealCase.lean: clear_shift_iff; the
  same reading rule; the cascade move is isMove_gate / nextOpening_gate).  At R = 1:
     residue 0      : blocked for every e in (-1,1)
     residue 1      : clear iff e >= 0
     residue 2..6   : clear
     residue 7      : clear iff e <= 0
  A move from R goes to the largest exit (8z+1)/rho_j over the blocked readings (z = the multiple of 8 nearest rho_j R).

Kernels.  A C int64/__int128 kernel (source embedded below, compiled with cc at run time into a temporary folder) runs the
cascade in integers: state R = a*m/y' with a = 8z+1; reading y blocked iff |a*y - 8*z*y'| < y'.  Its output is
cross-checked by (i) an independent least-clear-opening oracle inside the kernel (the least clear point among the
openings (8z+1)m/y, z >= 0, in [1, R*], compared with the cascade's landing: it does not use the move rule at all),
(ii) a Fraction re-implementation in this file on a full population (section 0).

Populations (all full, no sampling; sets of 7 distinct positive integers with gcd 1 and minimum m):
  A(N)   : every 7-subset of {1..N}.
  B(m,K) : minimum m, the other six any 6-subset of {m+1..K m}.
Counts are observations, never arguments.
"""
import os
import sys
import subprocess
import tempfile
import time
from fractions import Fraction as Fr
from collections import Counter, defaultdict
from itertools import combinations
from math import gcd, isqrt
from multiprocessing import Pool

C_SRC = r'''
#include <stdio.h>
#include <stdlib.h>
typedef long long ll; typedef __int128 LL;
static int N, mode, S[7], HI;
static ll cnt=0, mism=0, nofix=0, scalemis=0, scaletot=0;
#define MAXMV 5000
static int pr[MAXMV], pz[MAXMV]; static ll pa[MAXMV], py[MAXMV];
static ll gcdl(ll a, ll b){ while(b){ll t=a%b;a=b;b=t;} return a; }
static ll fl(LL x, LL d){ LL q=x/d; if((x%d!=0)&&((x<0)!=(d<0))) q--; return (ll)q; }
static int cascade(const int*s, ll *fa, ll *fy){
  ll a=1, yp=s[0]; int mv=0;
  for(;;){
    int best=-1; ll bz=0;
    for(int j=0;j<7;j++){
      ll y=s[j]; ll z=fl((LL)a*y+4*(LL)yp, 8*(LL)yp);
      ll dev=a*y-8*z*yp; if(dev<0)dev=-dev;
      if(dev<yp){
        if(best<0 || (LL)(8*z+1)*s[best] > (LL)(8*bz+1)*y){best=j;bz=z;}
      }
    }
    if(best<0){*fa=a;*fy=yp;return mv;}
    if(mv>=MAXMV) return -1;
    a=8*bz+1; yp=s[best]; pr[mv]=best; pz[mv]=(int)bz; pa[mv]=a; py[mv]=yp; mv++;
  }
}
static int oracle(const int*s, ll a, ll yp){
  ll m=s[0]; ll bc=-1, by=1;
  for(int j=0;j<7;j++){
    ll y=s[j];
    for(ll c=1;;c+=8){
      if((LL)c*yp > (LL)a*y) break;
      if(c*m<y) continue;
      int ok=1;
      for(int k=0;k<7&&ok;k++){ ll u=(c*s[k])%(8*y); if(u<y||u>7*y) ok=0; }
      if(ok){ if(bc<0 || (LL)c*by < (LL)bc*y){bc=c;by=y;} }
    }
  }
  return bc>=0 && (LL)bc*yp == (LL)a*by;
}
static void visit(void){
  ll g=0; for(int j=0;j<7;j++) g=gcdl(g,S[j]);
  ll fa,fy; int mv=cascade(S,&fa,&fy);
  if(mode==0){
    if(g!=1) return;
    cnt++;
    if(mv<0){nofix++; return;}
    if(!oracle(S,fa,fy)) mism++;
    printf("%d %d %d %d %d %d %d | %d |",S[0],S[1],S[2],S[3],S[4],S[5],S[6],mv);
    for(int i=0;i<mv;i++) printf(" %d:%d",pr[i],pz[i]);
    printf(" | %lld %lld\n",fa,fy);
  } else {
    if(g==1){cnt++; if(mv<0){nofix++;return;} if(!oracle(S,fa,fy)) mism++; return;}
    int r[7]; for(int j=0;j<7;j++) r[j]=S[j]/g;
    if(mv<0){nofix++;return;}
    static int rp[MAXMV],rz[MAXMV]; for(int i=0;i<mv;i++){rp[i]=pr[i];rz[i]=pz[i];}
    ll ra,ry; int mv2=cascade(r,&ra,&ry);
    scaletot++;
    int ok = (mv2==mv) && ra==fa;
    for(int i=0;ok&&i<mv;i++) if(rp[i]!=pr[i]||rz[i]!=pz[i]) ok=0;
    if(!ok) scalemis++;
  }
}
static void rec(int pos,int start){
  if(pos==7){visit();return;}
  for(int v=start; v<=HI-(6-pos); v++){S[pos]=v; rec(pos+1,v+1);}
}
int main(int argc,char**argv){
  char kind=argv[1][0];
  if(kind=='A'){N=atoi(argv[2]);mode=0;HI=N;rec(0,1);}
  else if(kind=='S'){N=atoi(argv[2]);mode=1;HI=N;rec(0,1);}
  else if(kind=='C'){ int m=atoi(argv[2]),K=atoi(argv[3]); mode=0; S[0]=m; for(int i=1;i<=4;i++) S[i]=(i+1)*m;
    for(int a=5*m+1;a<=K*m;a++) for(int b=a+1;b<=K*m;b++){S[5]=a;S[6]=b;visit();} }
  else { int m=atoi(argv[2]),K=atoi(argv[3]); N=K*m; mode=0; HI=N; S[0]=m; rec(1,m+1); }
  fprintf(stderr,"%lld %lld %lld %lld %lld\n",cnt,nofix,mism,scaletot,scalemis);
  return 0; }
'''

WORK = None
EXE = None


def build():
    global WORK, EXE
    WORK = tempfile.mkdtemp(prefix='aw_kernel_')
    src = os.path.join(WORK, 'aw.c')
    open(src, 'w').write(C_SRC)
    EXE = os.path.join(WORK, 'aw')
    subprocess.check_call(['cc', '-O2', '-o', EXE, src])
    os.environ['AW_EXE'] = EXE
    return EXE


def stream(args):
    """Yield (S, moves, path, final) for a population; the kernel's tail line is stored in stream.tail."""
    p = subprocess.Popen([os.environ['AW_EXE']] + [str(a) for a in args], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, bufsize=1 << 20)
    for line in p.stdout:
        a, b, c, d = line.split('|')
        S = tuple(map(int, a.split()))
        path = tuple((int(t.split(':')[0]), int(t.split(':')[1])) for t in c.split())
        yield S, int(b), path, tuple(map(int, d.split()))
    err = p.stderr.read()
    p.wait()
    stream.tail = tuple(map(int, err.split()))


stream.tail = None


# ---------------------------------------------------------------------------------------------------------------
# Independent Fraction cascade (same semantics as grid_deviation_landing_v1.py; used for section 0 and for the
# divergence explanations).  Move limit 400.
# ---------------------------------------------------------------------------------------------------------------
def frac_cascade(S, limit=400):
    m = S[0]
    rho = [Fr(y, m) for y in S]
    R = Fr(1)
    out = []
    states = []
    while True:
        bl = []
        for j, r in enumerate(rho):
            x = R * r
            z = (x / 8 + Fr(1, 2)).__floor__()
            if abs(x - 8 * z) < 1:
                bl.append((j, z, (8 * z + 1) / r))
        states.append((R, [(j, z) for j, z, _ in bl]))
        if not bl:
            return R, out, states
        j, z, nxt = max(bl, key=lambda t: t[2])
        out.append((j, z))
        R = nxt
        if len(out) >= limit:
            return None, out, states


def features(S):
    """Per other reading (rank 1..6): idx, e numerator over m, res, quo, sgn.  Tie rule: UP (e = -1/2)."""
    m = S[0]
    idx, en = [], []
    for y in S[1:]:
        q, r = divmod(y, m)
        t = 2 * r
        if t <= m and t != m:
            idx.append(q)
            en.append(r)
        else:
            idx.append(q + 1)
            en.append(r - m)
    return idx, en


def table_clear(res, en):
    if res == 0:
        return False
    if res == 1:
        return en >= 0
    if res == 7:
        return en <= 0
    return True


def sg(x):
    return (x > 0) - (x < 0)


# ---------------------------------------------------------------------------------------------------------------
# Population analysis (one process per population).
# ---------------------------------------------------------------------------------------------------------------
def label_of(res6):
    s = sorted(res6)
    if s == [2, 3, 4, 5, 6, 7]:
        return 'COMPLETE'
    z = s.count(0)
    if z:
        return 'ZERO x%d' % z
    if 1 in s:
        return 'NO0, residue 1 present (repeats d_min)'
    return 'NO0, NO1, repeated residue in 2..7'


def enc_path(path, with_lap=True):
    c = 0
    for r, z in path:
        c = c * 128 + (r * 16 + z + 1 if with_lap else r + 1)
    return c


def analyse_population(args):
    t0 = time.time()
    name = args_name(args)
    P = defaultdict(Counter)           # named counters
    ex = defaultdict(list)             # a few example sets per category
    dets = {}                          # determination dictionaries
    conflicts = defaultdict(set)
    names = ['rs>first_rank', 'rsq>first', 'rsq>rank_seq', 'rsq>last', 'rsq>path', 'blk(idx,sgn)>first',
             'blk(idx,sgn) no rank>opener class', 'multiset(rsq)>opener class']
    for n in names:
        dets[n] = {}
    classes_rs = set()
    classes_ms = set()
    total = 0
    for S, mv, path, fin in stream(args):
        total += 1
        m = S[0]
        idx, en = features(S)
        res = [i & 7 for i in idx]
        quo = [i >> 3 for i in idx]
        sgn = [sg(e) for e in en]
        # per-reading table against the direct reading (independent of idx)
        bl = []
        for j in range(6):
            y = S[j + 1]
            u = y % (8 * m)
            dclear = (m <= u <= 7 * m)
            tclear = table_clear(res[j], en[j])
            if dclear != tclear:
                P['table']['mismatch'] += 1
            if not dclear:
                bl.append(j)
        P['table']['readings'] += 6
        lonely = (mv == 0)
        P['identity']['lonely_iff_no_blocker_mismatch'] += int(lonely != (len(bl) == 0))
        # tie readings (rho = k + 1/2)
        if any(2 * (y % m) == m for y in S[1:]):
            P['ties']['sets_with_tie'] += 1
        lab = label_of(res)
        if len(ex['cls ' + lab + (' lonely' if lonely else ' moved')]) < 2:
            ex['cls ' + lab + (' lonely' if lonely else ' moved')].append((S, mv, path[:3]))
        P['class'][(lab, lonely)] += 1
        P['class_moves'][(lab, min(mv, 12))] += 1
        # sign pattern at the critical classes
        crit = tuple(sorted((res[j], sgn[j]) for j in range(6) if res[j] in (1, 7)))
        P['crit'][(lab, crit, lonely)] += 1
        if lab == 'COMPLETE':
            j7 = res.index(7)
            pred = sgn[j7] <= 0
            P['S2']['sets'] += 1
            P['S2']['pred_lonely_when_e7_le0'] += int(pred)
            P['S2']['exceptions'] += int(pred != lonely)
            P['S2'][('e7 sign', sgn[j7], 'lonely' if lonely else 'not lonely')] += 1
            if sgn[j7] > 0:
                P['S2']['fail_sets'] += 1
                if path and path[0][0] == j7 + 1:
                    P['S2']['fail_first_opener_is_res7'] += 1
                seq = []
                for r, z in path:
                    if r == 0:
                        seq.append(('dmin', z))
                    else:
                        seq.append((res[r - 1], z - quo[r - 1]))
                P['S2_seq'][tuple(seq)] += 1
                P['S2_nmoves'][len(path)] += 1
                # formula for the first exit  R1 = (idx_7 + 2)/(idx_7 + e_7) = (idx_7 + 2) m / y
                z0 = path[0][1]
                P['S2']['R1_formula_mismatch'] += int((8 * z0 + 1) != idx[j7] + 2)
                if len(path) == 1:
                    P['S2']['one_move_fail'] += 1
                if all(q == 0 for q in quo):
                    j6 = res.index(6)
                    cond = 9 * S[j6 + 1] > 7 * S[j7 + 1]
                    P['S2q0']['sets'] += 1
                    P['S2q0']['second_move_iff_9y6_gt_7y7_mismatch'] += int(cond != (len(path) >= 2))
                    if cond:
                        P['S2q0']['cond_true'] += 1
                        P['S2q0']['second_opener_is_res6_lap1_mismatch'] += int(path[1] != (j6 + 1, 1))
        if path:
            r0, z0 = path[0]
            # opener's data
            if r0 == 0:
                oc = ('dmin', 0, z0)
            else:
                oc = (res[r0 - 1], sgn[r0 - 1], z0 - quo[r0 - 1])
            P['first_class'][oc] += 1
            # lap = round(idx/8) = floor((idx+4)/8)
            if r0 >= 1:
                P['first_lap']['rule_mismatch'] += int(z0 != (idx[r0 - 1] + 4) // 8)
                rp = {0: 0, 1: 1, 7: -1}.get(res[r0 - 1])
                if rp is None:
                    P['first_lap']['opener_not_residue_0_1_7'] += 1
                else:
                    P['first_lap']['exit_numerator_mismatch'] += int(8 * z0 + 1 != idx[r0 - 1] - rp + 1)
            else:
                P['first_lap']['opener_is_dmin'] += 1
            # FM: the first opener is the argmax over blockers of the exit (idx - r + 1) m / (idx m + e m)
            if bl:
                bn = bd = None
                bj = -1
                for j in bl:
                    rp2 = {0: 0, 1: 1, 7: -1}.get(res[j])
                    if rp2 is None:
                        P['FM']['blocked_residue_not_0_1_7'] += 1
                        continue
                    nn = (idx[j] - rp2 + 1) * m
                    dd = idx[j] * m + en[j]
                    if bn is None or nn * bd > bn * dd:
                        bn, bd, bj = nn, dd, j
                    elif nn * bd == bn * dd:
                        P['FM']['equal_exit_ties'] += 1
                P['FM']['sets'] += 1
                P['FM']['argmax_mismatch'] += int(bj + 1 != r0)
            if bl:
                laps = {(idx[j] - {0: 0, 1: 1, 7: -1}.get(res[j], 0) + 0) // 8 for j in bl}
                if len(laps) == 1:
                    P['P1same']['sets_all_blockers_same_lap'] += 1
                    P['P1same']['lowest_blocker_opens'] += int(r0 == bl[0] + 1)
                else:
                    P['P1same']['sets_blockers_of_several_laps'] += 1
                    P['P1same']['lowest_blocker_opens_several_laps'] += int(r0 == bl[0] + 1)
            # P1: the first opener is the lowest-rank blocker
            if bl:
                low = bl[0] + 1
                ok = (r0 == low)
                P['P1']['sets_with_blocker'] += 1
                P['P1']['first_is_lowest_blocker'] += int(ok)
                if not ok:
                    types = tuple((res[j], sgn[j], idx[j]) for j in bl)
                    P['P1_viol_types'][tuple((res[j], sgn[j], quo[j]) for j in bl) + (('opener', bl.index(r0 - 1)),)] += 1
                    if len(ex['P1']) < 6:
                        ex['P1'].append((S, path[0], [(j + 1, idx[j], en[j]) for j in bl]))
            else:
                P['P1']['no_blocker_but_moved'] += 1
            lr, lz = path[-1]
            if lr == 0:
                lc = ('dmin', 0, lz)
            else:
                lc = (res[lr - 1], sgn[lr - 1], lz - quo[lr - 1])
            P['last_class'][(lab, lc)] += 1
            P['last_lap'][lz] += 1
            P['nmoves'][len(path)] += 1
        else:
            if bl:
                P['identity']['moved_zero_but_blockers'] += 1
        # class counts
        key_rs = 0
        key_rsq = 0
        codes = []
        for j in range(6):
            c = res[j] * 3 + sgn[j] + 1
            codes.append(c * 16 + min(quo[j], 15))
            key_rs = key_rs * 24 + c
            key_rsq = key_rsq * 384 + c * 16 + min(quo[j], 15)
        classes_rs.add(key_rs)
        classes_ms.add(tuple(sorted(c // 16 for c in codes)))
        key_ms = 0
        for c in sorted(codes):
            key_ms = key_ms * 384 + c
        first_rank = (path[0][0] + 1) if path else 0
        first = ((path[0][0] + 1) * 64 + path[0][1]) if path else 0
        last = ((path[-1][0] + 1) * 64 + path[-1][1]) if path else 0
        rseq = enc_path(path, False)
        full = enc_path(path, True)
        if path:
            r0, z0 = path[0]
            ocode = (99 if r0 == 0 else (res[r0 - 1] * 3 + sgn[r0 - 1] + 1)) * 64 + (z0 - (0 if r0 == 0 else quo[r0 - 1])) + 8
        else:
            ocode = 0
        kb = tuple((j, idx[j], sgn[j]) for j in bl)
        kb_nr = tuple((idx[j], sgn[j]) for j in bl)
        for nm, k, o in (('rs>first_rank', key_rs, first_rank), ('rsq>first', key_rsq, first),
                         ('rsq>rank_seq', key_rsq, rseq), ('rsq>last', key_rsq, last), ('rsq>path', key_rsq, full),
                         ('blk(idx,sgn)>first', kb, first),
                         ('blk(idx,sgn) no rank>opener class', kb_nr, ocode),
                         ('multiset(rsq)>opener class', key_ms, ocode)):
            d = dets[nm]
            v = d.get(k)
            if v is None:
                d[k] = o
            elif v != o and v != -1:
                d[k] = -1
                conflicts[nm].add(k)
    tail = stream.tail
    out = {'name': name, 'total': total, 'tail': tail, 'P': P, 'ex': ex,
           'distinct_rs': len(classes_rs), 'distinct_ms': len(classes_ms),
           'keys': {n: len(dets[n]) for n in names},
           'conf': {n: len(conflicts[n]) for n in names},
           'conf_keys': {n: conflicts[n] for n in ('rsq>path', 'rsq>first', 'rs>first_rank', 'rsq>last', 'blk(idx,sgn)>first')},
           'secs': time.time() - t0}
    return out


def args_name(args):
    if args[0] == 'A':
        return 'A(%s)' % args[1]
    return '%s(%s,%s)' % (args[0], args[1], args[2])


# ---------------------------------------------------------------------------------------------------------------
# Pass 2: sets inside conflicting keys of rsq>path (counts, divergence explanation).
# ---------------------------------------------------------------------------------------------------------------
def enc_rsq(S):
    idx, en = features(S)
    k = 0
    for j in range(6):
        c = (idx[j] & 7) * 3 + sg(en[j]) + 1
        k = k * 384 + c * 16 + min(idx[j] >> 3, 15)
    return k


def pass2(args, ckeys):
    firsts = {}
    sets_in = 0
    pairs = []
    for S, mv, path, fin in stream(args):
        k = enc_rsq(S)
        if k in ckeys:
            sets_in += 1
            f = firsts.get(k)
            if f is None:
                firsts[k] = (S, path)
            elif f is not False and f[1] != path:
                pairs.append((f[0], S))
                firsts[k] = False
    return sets_in, pairs


def pass2b(args, ckeys):
    """Pairs of sets with the same blocked-reading key (idx, sign) and different first opener."""
    firsts = {}
    pairs = []
    for S, mv, path, fin in stream(args):
        if not path:
            continue
        m = S[0]
        idx, en = features(S)
        res = [i & 7 for i in idx]
        bl = [j for j in range(6) if not (m <= S[j + 1] % (8 * m) <= 7 * m)]
        kb = tuple((j, idx[j], sg(en[j])) for j in bl)
        if kb in ckeys:
            f = firsts.get(kb)
            if f is None:
                firsts[kb] = (S, path[0])
            elif f is not False and f[1] != path[0]:
                pairs.append((f[0], S, f[1], path[0]))
                firsts[kb] = False
    return pairs


def explain(S1, S2):
    R1, p1, st1 = frac_cascade(S1)
    R2, p2, st2 = frac_cascade(S2)
    k = 0
    while k < min(len(p1), len(p2)) and p1[k] == p2[k]:
        k += 1
    b1 = st1[k][1] if k < len(st1) else None
    b2 = st2[k][1] if k < len(st2) else None
    cat = 'blocked sets differ' if b1 != b2 else 'same blocked set, different exit chosen'
    diff = sorted(set(b1) ^ set(b2)) if b1 != b2 else []
    return k + 1, cat, diff, (st1[k][0], st2[k][0]), b1, b2, p1, p2


# ---------------------------------------------------------------------------------------------------------------
# Q(sqrt 2) arithmetic for the non-rational test (section 10).
# ---------------------------------------------------------------------------------------------------------------
class QS:
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(s, o):
        o = o if isinstance(o, QS) else QS(o)
        return QS(s.a + o.a, s.b + o.b)

    def __sub__(s, o):
        o = o if isinstance(o, QS) else QS(o)
        return QS(s.a - o.a, s.b - o.b)

    def __mul__(s, o):
        o = o if isinstance(o, QS) else QS(o)
        return QS(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)

    def inv(s):
        n = s.a * s.a - 2 * s.b * s.b
        return QS(s.a / n, -s.b / n)

    def __truediv__(s, o):
        o = o if isinstance(o, QS) else QS(o)
        return s * o.inv()

    def sign(s):
        a, b = s.a, s.b
        if b == 0:
            return sg(a)
        if a == 0:
            return sg(b)
        if (a > 0) == (b > 0):
            return sg(a)
        # opposite signs: compare a^2 with 2 b^2 (never equal: sqrt 2 irrational)
        return sg(a) if a * a > 2 * b * b else sg(b)

    def __lt__(s, o):
        return (s - o).sign() < 0

    def __le__(s, o):
        return (s - o).sign() <= 0

    def floor(s):
        d = s.a.denominator * s.b.denominator // gcd(s.a.denominator, s.b.denominator)
        p = int(s.a * d)
        q = int(s.b * d)
        if q == 0:
            return p // d
        t = isqrt(2 * q * q)               # floor of sqrt(2 q^2); 2 q^2 is never a square
        n = p + t if q > 0 else p - t - 1
        return n // d

    def __eq__(s, o):
        o = o if isinstance(o, QS) else QS(o)
        return s.a == o.a and s.b == o.b

    def __hash__(s):
        return hash((s.a, s.b))


def qs_cascade(rho, limit=400):
    R = QS(1)
    out = []
    eight = QS(8)
    while True:
        bl = []
        for j, r in enumerate(rho):
            x = R * r
            z = (x / eight + Fr(1, 2)).floor()
            dv = x - QS(8 * z)
            if (dv.sign() >= 0 and dv < QS(1)) or (dv.sign() < 0 and QS(-1) < dv):
                bl.append((j, z, (QS(8 * z + 1)) / r))
        if not bl:
            return R, out
        best = bl[0]
        for t in bl[1:]:
            if best[2] < t[2]:
                best = t
        out.append((best[0], best[1]))
        R = best[2]
        if len(out) >= limit:
            return None, out


def qs_oracle(rho, Rstar):
    """Least clear opening in [1, R*]: independent of the move rule."""
    best = None
    for j, rj in enumerate(rho):
        c = 1
        while True:
            cand = QS(c) / rj
            if Rstar < cand:
                break
            if not (cand < QS(1)):
                ok = True
                for rk in rho:
                    x = rk * cand
                    u = x - QS(8 * (x / QS(8)).floor())
                    if u < QS(1) or QS(7) < u:
                        ok = False
                        break
                if ok and (best is None or cand < best):
                    best = cand
            c += 8
    return best


def qs_test(arg):
    chunk, nchunks, npool = arg
    s2 = QS(0, 1)
    op = (s2 - 1) * Fr(1, 2)           # +0.2071
    om = (s2 - 1) * Fr(-1, 3)          # -0.1381
    base = [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 17]
    pool = []
    for k in base:
        pool.append(QS(k) + op)
        pool.append(QS(k) + om)
    res = Counter()
    first_lonely_checked = 0
    pool = pool[:npool]
    for ci, six in enumerate(combinations(pool, 6)):
        if ci % nchunks != chunk:
            continue
        rho = [QS(1)] + sorted(six, key=lambda q: (q.a + q.b * Fr(14142135623730951, 10 ** 16)))
        # exact order check
        for i in range(6):
            assert rho[i] < rho[i + 1] or rho[i] == rho[i + 1] and False
        Rst, path = qs_cascade(rho)
        res['sets'] += 1
        if Rst is None:
            res['nofix'] += 1
            continue
        orc = qs_oracle(rho, Rst)
        res['oracle_mismatch'] += int(orc is None or not (orc == Rst))
        # normal form
        blocked = []
        info = []
        for j in range(1, 7):
            r = rho[j]
            idx = (r + Fr(1, 2)).floor()
            e = r - QS(idx)
            es = e.sign()
            rs = idx % 8
            tclear = table_clear(rs, es)
            x = r - QS(8 * (r / QS(8)).floor())
            dclear = not (x < QS(1) or QS(7) < x)
            res['table_mismatch'] += int(tclear != dclear)
            info.append((idx, es, rs))
            if not dclear:
                blocked.append(j)
        res['lonely_iff_noblocker_mismatch'] += int((len(path) == 0) != (len(blocked) == 0))
        if path:
            j0, z0 = path[0]
            if j0 >= 1:
                idx, es, rs = info[j0 - 1]
                res['lap_rule_mismatch'] += int(z0 != (idx + 4) // 8)
                rp = {0: 0, 1: 1, 7: -1}.get(rs)
                if rp is None:
                    res['opener_not_res_0_1_7'] += 1
                else:
                    res['exit_numerator_mismatch'] += int(8 * z0 + 1 != idx - rp + 1)
        rss = sorted(i[2] for i in info)
        if rss == [2, 3, 4, 5, 6, 7]:
            res['complete'] += 1
            j7 = [i[2] for i in info].index(7)
            res['complete_S2_exceptions'] += int((info[j7][1] <= 0) != (len(path) == 0))
    return dict(res)


# ---------------------------------------------------------------------------------------------------------------
# Hypothesis tests on A(24) / A(14) (pure integer, Python): rounding rules, units.

WILD_EX = []


def rounding_variant_test(N):
    variants = ['nearest, tie up', 'nearest, tie down', 'floor (e in [0,1))', 'ceil (e in (-1,0])',
                'wild: nearest + (-1,0,+1 by rank), |e| up to 3/2']
    R = {v: Counter() for v in variants}
    for S in combinations(range(1, N + 1), 7):
        g = 0
        for y in S:
            g = gcd(g, y)
        if g != 1:
            continue
        m = S[0]
        direct = [(m <= (y % (8 * m)) <= 7 * m) for y in S[1:]]
        lonely = all(direct)
        for v in variants:
            idx, en = [], []
            for jj, y in enumerate(S[1:]):
                q, r = divmod(y, m)
                if v == 'floor (e in [0,1))':
                    i, e = q, r
                elif v == 'ceil (e in (-1,0])':
                    i, e = (q, 0) if r == 0 else (q + 1, r - m)
                else:
                    if 2 * r < m:
                        i, e = q, r
                    elif 2 * r > m:
                        i, e = q + 1, r - m
                    else:
                        i, e = (q + 1, r - m) if v != 'nearest, tie down' else (q, r)
                    if v.startswith('wild'):
                        s_ = (-1, 0, 1)[jj % 3]
                        i, e = i + s_, e - s_ * m
                idx.append(i)
                en.append(e)
            res = [i % 8 for i in idx]
            ident = [m <= ((res[j] * m + en[j]) % (8 * m)) <= 7 * m for j in range(6)]
            R[v]['identity_mismatch'] += int(ident != direct)
            tab = [table_clear(res[j], en[j]) for j in range(6)]
            R[v]['simple_table_reading_mismatch'] += sum(int(tab[j] != direct[j]) for j in range(6))
            R[v]['sets'] += 1
            R[v]['max_abs_e_x2'] = max(R[v]['max_abs_e_x2'], max(abs(2 * e) * 1000 // m for e in en))
            for j in range(6):
                if not direct[j]:
                    R[v]['blocked_readings'] += 1
                    if res[j] not in (0, 1, 7):
                        R[v]['blocked_residue_not_0_1_7'] += 1
                    ztrue = (S[j + 1] + 4 * m) // (8 * m)
                    R[v]['lap_formula_mismatch'] += int(ztrue != (idx[j] + 4) // 8)
            if sorted(res) == [2, 3, 4, 5, 6, 7]:
                R[v]['complete'] += 1
                j7 = res.index(7)
                R[v]['S2_exceptions'] += int((en[j7] <= 0) != lonely)
                if (en[j7] <= 0) != lonely and len(WILD_EX) < 3 and v.startswith('wild'):
                    WILD_EX.append((S, idx, [Fr(e, m) for e in en]))
    return R




def unit_test(N):
    """Gate at 1/(8 u) for every disparity u (not only d_min): table vs direct reading, and lonely counts."""
    R = Counter()
    for S in combinations(range(1, N + 1), 7):
        g = 0
        for y in S:
            g = gcd(g, y)
        if g != 1:
            continue
        for k, u in enumerate(S):
            lonely = True
            for y in S:
                if y == u:
                    continue
                q, r = divmod(y, u)
                if 2 * r < u:
                    idx, en = q, r
                elif 2 * r > u:
                    idx, en = q + 1, r - u
                else:
                    idx, en = q + 1, r - u
                dclear = (u <= (y % (8 * u)) <= 7 * u)
                tclear = table_clear(idx % 8, en)
                R['table_mismatch'] += int(dclear != tclear)
                R['readings'] += 1
                if not dclear:
                    lonely = False
            R[('unit rank', k, 'lonely at 1/(8u)')] += int(lonely)
        R['sets'] += 1
    return R


def fraction_recheck(N):
    bad = 0
    tot = 0
    for S, mv, path, fin in stream(['A', N]):
        Rst, p, _ = frac_cascade(S)
        tot += 1
        if Rst is None or p != list(path) or Rst != Fr(fin[0] * S[0], fin[1]):
            bad += 1
    return tot, bad


# ---------------------------------------------------------------------------------------------------------------
def fmt_counter(c, top=None, indent='   '):
    items = sorted(c.items(), key=lambda t: (-t[1], str(t[0])))
    if top:
        items = items[:top]
    return '\n'.join('%s%s : %d' % (indent, k, v) for k, v in items)


def sec(title):
    print()
    print('=' * 118)
    print(title)
    print('=' * 118)

def pairwise_cells():
    """Exact pairwise comparison of two blocked readings at R = 1: which exit is larger.
    Population: idx in 2..59, e = n/24 with n in -12..11 (tie rho = k+1/2 rounded up), every pair of blocked readings with rho_a < rho_b."""
    D = 24
    items = []
    for idx in range(2, 60):
        for n in range(-D // 2, D // 2):
            r = idx % 8
            if not (r == 0 or (r == 1 and n < 0) or (r == 7 and n > 0)):
                continue
            rho = Fr(idx * D + n, D)
            if rho <= 1:
                continue
            rp = {0: 0, 1: 1, 7: -1}[r]
            z = (idx - rp) // 8
            items.append((idx, n, rho, (8 * z + 1) / rho, z, r))
    cells = defaultdict(set)
    ex = {}
    same_z_bad = 0
    same_z = 0
    for a in items:
        for b in items:
            if a[2] < b[2]:
                key = (a[0], sg(a[1]), b[0], sg(b[1]))
                win = 'low' if a[3] > b[3] else ('high' if a[3] < b[3] else 'tie')
                cells[key].add(win)
                ex.setdefault((key, win), (a, b))
                if a[4] == b[4]:
                    same_z += 1
                    same_z_bad += int(win != 'low')
    dep = [k for k, v in cells.items() if len(v) > 1]
    typ = defaultdict(set)
    for (i1, s1, i2, s2), w in cells.items():
        r1, r2 = i1 % 8, i2 % 8
        rp1, rp2 = {0: 0, 1: 1, 7: -1}[r1], {0: 0, 1: 1, 7: -1}[r2]
        z1, z2 = (i1 - rp1) // 8, (i2 - rp2) // 8
        typ[((r1, s1), z1, (r2, s2), z2)] |= w
    deptyp = {k: v for k, v in typ.items() if len(v) > 1}
    return len(items), len(cells), len(dep), len(typ), deptyp, ex, same_z, same_z_bad, cells


def structure_growth():
    out = []
    for N in (16, 20, 24, 28):
        T = Counter()
        T2 = Counter()
        mx = 0
        for S, mv, path, fin in stream(['A', N]):
            if not path:
                continue
            idx, en = features(S)
            res = [i & 7 for i in idx]
            quo = [i >> 3 for i in idx]
            seq = tuple(('d', z) if r == 0 else (res[r - 1], z - quo[r - 1]) for r, z in path)
            seq2 = tuple(('d', z) if r == 0 else (res[r - 1], sg(en[r - 1]), z - quo[r - 1]) for r, z in path)
            T[seq] += 1
            T2[seq2] += 1
            mx = max(mx, len(path))
        out.append((N, len(T), len(T2), mx))
    return out


def refinement_test(args):
    """Key (idx, floor(K e)) by rank for nested K = 1 (sign only), 2, 4, ..., exact; outcome: full path."""
    sets = []
    for S, mv, path, fin in stream(args):
        sets.append((S, path))
    out = []
    for K in (1, 2, 4, 8, 16, 32, 64, 128, 1024, 720720):
        d = {}
        conf = set()
        for S, path in sets:
            m = S[0]
            idx, en = features(S)
            key = tuple((idx[j], (en[j] * K) // m if K > 1 else sg(en[j])) for j in range(6))
            v = d.get(key)
            if v is None:
                d[key] = path
            elif v != path:
                conf.add(key)
        out.append((K, len(d), len(conf)))
    return out


def main():
    t_start = time.time()
    quick = bool(os.environ.get('AW_QUICK'))
    build()
    print('grid_deviation_normal_form_v1.py   (task AW; exact; Rules 1,5,6,7,13,15,16,18,21)')
    print('Rounding rule used for idx: nearest integer, tie rho = k+1/2 rounded UP (e = -1/2).  Section 9 tests the other rules.')
    print('Grades: [OBS] exact observation on the stated full population; [reasoned] argument not formalised here; [L] Lean theorem in')
    print('LonelyRunnerFresh/Fresh (cited, not proved here).  Counts are observations, never arguments.')

    # ---------------------------------------------------------------- 0
    sec('0. Cross-checks of the kernel before any figure is used')
    tot, bad = fraction_recheck(14 if quick else 18)
    print('Fraction cascade (this file) against the integer kernel, full population A(%d): sets %d, path/landing mismatches %d  [OBS]' % (14 if quick else 18, tot, bad))
    print('Independent least-clear-opening oracle (inside the kernel, no move rule): mismatches per population in the next table.')
    print('Existing record to compare: experiments/n8/grid_deviation_landing_v1.out (N=24 moves histogram).')
    if quick:
        pops = [['A', 16], ['A', 18], ['B', 2, 8], ['B', 3, 6], ['B', 4, 5], ['B', 5, 4], ['C', 4, 12]]
    else:
        pops = [['A', 24], ['A', 28], ['B', 2, 20], ['B', 3, 12], ['B', 4, 10], ['B', 5, 8]] + \
               [['C', m, 60] for m in (3, 4, 5, 6, 7, 8, 9, 10, 12)]
    with Pool(3) as pool:
        results = pool.map(analyse_population, pops, chunksize=1)
    byname = {r['name']: r for r in results}
    A0 = results[0]
    sec('Populations: sets, move-limit failures, oracle mismatches, table-vs-direct reading mismatches')
    print('Populations (all 7-sets of integers, gcd 1, minimum m = d_min): A(N) = all 7-subsets of {1..N}; B(m,K) = minimum m, the other six any 6-subset of {m+1..Km};')
    print('C(m,K) = minimum m, four fixed readings 2m,3m,4m,5m (residues 2..5, e = 0, always clear), two free readings y in (5m, Km] (every pair).')
    for r in results:
        t = r['tail']
        print('%-9s sets %9d  no fixed point within the move limit %d  oracle mismatches %d  reading-table mismatches %d / %d  lonely<->no-blocker mismatches %d  (%.0fs)' %
              (r['name'], r['total'], t[1], t[2], r['P']['table'].get('mismatch', 0), r['P']['table'].get('readings', 0),
               r['P']['identity'].get('lonely_iff_no_blocker_mismatch', 0) + r['P']['identity'].get('moved_zero_but_blockers', 0), r['secs']))
    print('   moves histogram of %s (compare grid_deviation_landing_v1.out):' % A0['name'], sorted(A0['P']['nmoves'].items()),
          ' lonely at R=1 (zero moves):', A0['total'] - sum(A0['P']['nmoves'].values()))

    # ---------------------------------------------------------------- 1
    sec('1. Classification by residue pattern (the six readings other than d_min, idx = 1, e = 0)')
    print('Classes: COMPLETE = residues exactly {2..7};  ZERO xk = k readings of residue 0 (a D_max-shifted runner; blocked for every |e|<1);')
    print('         NO0 with residue 1 present (a second reading on the residue of d_min);  NO0, NO1 with a repeated residue in 2..7.')
    for r in results[:6]:
        print()
        print('--- %s   (%d sets)' % (r['name'], r['total']))
        cls = r['P']['class']
        labs = sorted({k[0] for k in cls})
        print('   %-42s %10s %10s %10s' % ('class', 'sets', 'lonely@1', 'moved'))
        for lab in labs:
            a = cls.get((lab, True), 0)
            b = cls.get((lab, False), 0)
            print('   %-42s %10d %10d %10d' % (lab, a + b, a, b))
    print()
    print('Number of moves by class, %s:' % results[1]['name'])
    cm = results[1]['P']['class_moves']
    for lab in sorted({k[0] for k in cm}):
        print('   %-42s %s' % (lab, [(n, cm[(lab, n)]) for n in range(13) if (lab, n) in cm]))
    print()
    print('Statement CR [reasoned from the reading identity; OBS on all populations]: lonely at R = 1 iff no reading has residue 0, none has residue 1 with e < 0,')
    print('none has residue 7 with e > 0.  Residues 2..6 are clear for every |e| <= 1/2.')
    tot_exc = sum(r['P']['identity'].get('lonely_iff_no_blocker_mismatch', 0) + r['P']['identity'].get('moved_zero_but_blockers', 0) for r in results)
    tab_exc = sum(r['P']['table'].get('mismatch', 0) for r in results)
    print('   CR exceptions over all %d populations (%d sets): %d;  reading-table mismatches over %d readings: %d  [OBS]' % (
        len(results), sum(r['total'] for r in results), tot_exc, sum(r['P']['table'].get('readings', 0) for r in results), tab_exc))
    print('   Sign pattern of the critical readings (residue-1 and residue-7 readings only) with the class and the outcome, %s, top 22:' % A0['name'])
    print(fmt_counter(Counter({k: v for k, v in A0['P']['crit'].items()}), top=22))
    print('   Concrete sets (first seen) per class and outcome, %s: (set, number of moves, first moves as (rank, lap)):' % A0['name'])
    for k in sorted(A0['ex']):
        if k.startswith('cls '):
            print('      %-62s %s' % (k, A0['ex'][k]))

    # ---------------------------------------------------------------- 2
    sec('2. COMPLETE sets: R = 1 is lonely iff the residue-7 reading has e <= 0')
    for r in results:
        S2 = r['P']['S2']
        print('%-9s COMPLETE sets %6d: exceptions to (lonely at R=1 <=> e_7 <= 0): %d  | e7<0 lonely %d, e7=0 lonely %d, e7>0 lonely %d, e7>0 not lonely %d' % (
            r['name'], S2.get('sets', 0), S2.get('exceptions', 0),
            S2.get(('e7 sign', -1, 'lonely'), 0), S2.get(('e7 sign', 0, 'lonely'), 0),
            S2.get(('e7 sign', 1, 'lonely'), 0), S2.get(('e7 sign', 1, 'not lonely'), 0)))
    print()
    print('When e_7 > 0 (z = Q+1, Q = floor(idx_7/8)):')
    print('   rho_7 R = idx_7 + e_7 sits in (8Q+7, 8Q+8), so delta = sres8 = e_7 - 1 in (-1,-1/2]   (the brief wrote delta = e; the residue of the reading is e - 1, since idx_7 = 7 mod 8),')
    print('   first move  R1 = 1 + (1-delta)/rho_7 = 1 + (2-e_7)/(idx_7+e_7) = (idx_7+2)/(idx_7+e_7) = (8Q+9)/rho_7   [L: RealCase.nextOpening_gate with delta = e - 1; OBS below].')
    fs = Counter()
    for r in results:
        S2 = r['P']['S2']
        fs.update({'fail': S2.get('fail_sets', 0), 'res7_first': S2.get('fail_first_opener_is_res7', 0),
                   'numerator_mismatch': S2.get('R1_formula_mismatch', 0), 'single_move': S2.get('one_move_fail', 0)})
        print('   %-9s failing COMPLETE sets %6d: first opener is the residue-7 reading in %6d;  numerator 8z+1 = idx_7+2 mismatches %d;  landing after that single move: %d' % (
            r['name'], S2.get('fail_sets', 0), S2.get('fail_first_opener_is_res7', 0), S2.get('R1_formula_mismatch', 0), S2.get('one_move_fail', 0)))
    print('   totals:', dict(fs))
    print('   After the move the other readings are rho_j R1 = rho_j (8Q+9)/rho_7 (new unit D1 = d_7/(8Q+9)); the move multiplies R by at most 9/7.')
    q0 = Counter()
    for r in results:
        q0.update(r['P']['S2q0'])
    print('   Quotient-zero failing COMPLETE sets (idx = 2,...,7 exactly): sets %d; second move happens iff 9 d_6 > 7 d_7 (d_6, d_7 the residue-6 and residue-7 disparities): mismatches %d;' % (
        q0['sets'], q0['second_move_iff_9y6_gt_7y7_mismatch']))
    print('      when it happens the second opener is the residue-6 reading at lap 1: cases %d, mismatches %d   [OBS; derivation: s_6 = 9 rho_6/rho_7 lies in (7,9) iff 9 rho_6 > 7 rho_7, and no lower reading reaches 7 at e >= -1/2 [reasoned]]' % (
        q0['cond_true'], q0['second_opener_is_res6_lap1_mismatch']))
    print('   What happens next: openers of the failing COMPLETE sets, per move (residue of the opener, lap - quotient of the opener); "dmin" = the unit reading as an opener:')
    for r in [A0, byname.get('B(3,12)', results[min(3, len(results) - 1)])]:
        print('   --- %s: number of moves histogram %s' % (r['name'], sorted(r['P']['S2_nmoves'].items())))
        print(fmt_counter(r['P']['S2_seq'], top=12, indent='      '))
        lastc = Counter()
        for seq, v in r['P']['S2_seq'].items():
            lastc[seq[-1]] += v
        print('      landing opener (residue, lap-quotient) over the failing COMPLETE sets:', sorted(lastc.items(), key=lambda t: -t[1]))

    # ---------------------------------------------------------------- 3
    sec('3. Sets with R = 1 blocked: the first move against the residue/sign/quotient coordinates')
    print('FM (first move): the opener is the blocked reading with the largest exit (idx - r + 1)/(idx + e), r = signed residue (0, +1, -1 for residue 0, 1, 7);')
    print('its lap is z = round(idx/8) = floor((idx+4)/8).  [exit = (8z+1)/rho_j = 1 + (1-delta)/rho_j with delta = r + e: RealCase.nextOpening_gate]')
    for r in results:
        P1 = r['P']['P1']
        fl = r['P']['first_lap']
        FM = r['P']['FM']
        print('%-9s moved %8d | FM argmax mismatches %d (equal-exit ties %d) | lap rule mismatches %d | exit numerator mismatches %d | blocked reading not of residue 0/1/7: %d | '
              'P1 lowest-rank blocker opens: %d of %d' % (
                  r['name'], P1.get('sets_with_blocker', 0), FM.get('argmax_mismatch', 0), FM.get('equal_exit_ties', 0),
                  fl.get('rule_mismatch', 0), fl.get('exit_numerator_mismatch', 0), FM.get('blocked_residue_not_0_1_7', 0),
                  P1.get('first_is_lowest_blocker', 0), P1.get('sets_with_blocker', 0)))
    tot1 = Counter()
    for r in results:
        tot1.update(r['P']['P1same'])
    print('   When all blocked readings lie in ONE zone (same lap z): the lowest-rank blocker opens in %d of %d sets (all populations);' % (
        tot1['lowest_blocker_opens'], tot1['sets_all_blockers_same_lap']))
    print('   when they lie in several zones: the lowest-rank blocker opens in %d of %d sets.   [OBS]' % (
        tot1['lowest_blocker_opens_several_laps'], tot1['sets_blockers_of_several_laps']))
    print()
    print('First opener class (residue, sign of e, lap - quotient) with counts:')
    for r in [byname.get('A(28)', results[1]), byname.get('B(3,12)', results[3])]:
        print('   --- %s' % r['name'])
        print(fmt_counter(r['P']['first_class'], indent='      '))
    print()
    print('Violations of P1 (the opener is not the lowest-rank blocker): blockers as (residue, sign, quotient) in rank order, then the index of the opener among them:')
    for r in results:
        v = r['P']['P1_viol_types']
        if not v:
            continue
        print('   --- %s: %d sets in %d blocker-type signatures' % (r['name'], sum(v.values()), len(v)))
        print(fmt_counter(v, top=8, indent='      '))
        for e in r['ex'].get('P1', [])[:3]:
            print('      example S=%s  first opener (rank,lap)=%s  blockers (rank, idx, e*m) %s' % e)
    print('   Reason [reasoned, exact]: the exit of a blocker is (8z+1)/rho = 1 + (1-delta)/rho with 1-delta in (0, 1/2] for a residue-1 reading (e<0), in [1/2,3/2] for residue 0, in [3/2,2) for residue 7;')
    print('   a lower reading with a small numerator and a smaller lap can lose to a higher reading of a larger lap.  So "lowest-rank blocker opens" is NOT a rule; the max-exit rule FM is.')
    print()
    nitems, ncells, ndep, ntyp, deptyp, pex, same_z, same_z_bad, cells = pairwise_cells()
    print('3b. Pairwise exact test of FM against (idx, sign) -- population: idx 2..59, e = n/24 (n = -12..11), all blocked readings, every pair with rho_a < rho_b')
    print('   blocked readings %d; cells (idx_a, sign_a, idx_b, sign_b): %d; cells in which BOTH readings can win depending on |e| alone: %d (%d structural types (res,sign,lap) pairs of %d)' % (
        nitems, ncells, ndep, len(deptyp), ntyp))
    print('   same lap (z_a = z_b): pairs %d, in which the lower reading does not win: %d   [OBS; reasoned: equal numerators 8z+1, smaller rho gives the larger exit]' % (same_z, same_z_bad))
    tc = Counter()
    for (ta, za, tb, zb), v in deptyp.items():
        tc[(ta, tb)] += 1
    print('   structural pair types with a magnitude-dependent winner (type = (residue, sign of e)), number of lap pairs:')
    print(fmt_counter(tc, indent='      '))
    shown = 0
    for (ta, za, tb, zb), v in sorted(deptyp.items(), key=lambda t: (t[0][1], t[0][3])):
        if shown >= 4:
            break
        shown += 1
        cell_keys = [k for k in cells if (k[0] % 8 == ta[0] and sg(k[1]) == ta[1] and k[2] % 8 == tb[0])]
        print('   type %s lap %d vs %s lap %d: winners %s ; the lower wins iff (8*%d+1) rho_b > (8*%d+1) rho_a' % (ta, za, tb, zb, sorted(v), za, zb))
    for key in list(pex)[:0]:
        pass
    print('   Exact thresholds (the winner flips inside one (idx, sign) cell): the higher reading b wins iff (8 z_b+1) rho_a > ... i.e. iff (8 z_a+1) rho_b < (8 z_b+1) rho_a, i.e. e_b < t(e_a) with')
    print('      t(e_a) = (8 z_b+1)(idx_a+e_a)/(8 z_a+1) - idx_b:')
    seen = set()
    for (ta, za, tb, zb) in sorted(deptyp, key=lambda t: (t[1], t[3], t[0], t[2])):
        for (k, w), (a, b) in sorted(pex.items(), key=lambda t: (t[0][0], t[0][1])):
            if k[0] % 8 == ta[0] and sg(a[1]) == ta[1] and a[4] == za and k[2] % 8 == tb[0] and sg(b[1]) == tb[1] and b[4] == zb and (ta, za, tb, zb) not in seen:
                seen.add((ta, za, tb, zb))
                ea = Fr(a[1], 24)
                t_ = Fr(8 * zb + 1, 8 * za + 1) * (a[0] + ea) - b[0]
                print('      a = (idx %d, e_a = %s), b = idx %d, laps %d,%d: higher wins iff e_b < %s  (cell winners %s)' % (a[0], ea, b[0], za, zb, t_, sorted(deptyp[(ta, za, tb, zb)])))
        if len(seen) >= 6:
            break
    for args, r in zip(pops, results):
        if r['name'] in ('C(5,60)', 'C(7,60)') and r['conf_keys']['blk(idx,sgn)>first']:
            prs = pass2b(args, r['conf_keys']['blk(idx,sgn)>first'])
            print('   --- %s: %d keys (blocked readings (rank, idx, sign)) with two different first openers; first three, exact:' % (r['name'], len(prs)))
            for S1, S2_, f1, f2 in prs[:3]:
                m1, m2 = S1[0], S2_[0]
                print('      S1=%s first opener (rank,lap)=%s | S2=%s first opener %s' % (S1, f1, S2_, f2))
                for S, f in ((S1, f1), (S2_, f2)):
                    mm = S[0]
                    bl_ = [j for j in range(1, 7) if not (mm <= S[j] % (8 * mm) <= 7 * mm)]
                    desc = []
                    for j in bl_:
                        rho_ = Fr(S[j], mm)
                        z_ = (rho_ / 8 + Fr(1, 2)).__floor__()
                        desc.append('rank %d: rho=%s lap %d exit %s' % (j, rho_, z_, (8 * z_ + 1) / rho_))
                    print('         ' + ' ; '.join(desc))
    print('   So the coordinates that fix the first opener are the blocked readings (idx, e) -- the sign of e fixes it only inside the cells where the pairwise winner is constant;')
    print('   the populations A, B above realise only e values with few denominators and show no magnitude dependence there; the pairwise test shows the dependence exists [OBS, exact].')
    print()
    cj = Counter()
    print('Population C (two free readings above four clear ones): first opener against the blocked readings (idx, sign) only:')
    for r in results:
        if r['name'].startswith('C('):
            print('   %-9s sets %7d  keys blk(idx,sgn)>first: %5d conflicts %d | rsq>first conflicts %d | FM mismatches %d | P1 holds %d of %d' % (
                r['name'], r['total'], r['keys']['blk(idx,sgn)>first'], r['conf']['blk(idx,sgn)>first'], r['conf']['rsq>first'],
                r['P']['FM'].get('argmax_mismatch', 0), r['P']['P1'].get('first_is_lowest_blocker', 0), r['P']['P1'].get('sets_with_blocker', 0)))
    print()
    print('Landing (the last opener): class (residue, sign, lap - quotient) by set class, %s, top 30:' % results[1]['name'])
    lc = Counter()
    for (lab, c), v in results[1]['P']['last_class'].items():
        lc[(lab, c)] += v
    print(fmt_counter(lc, top=30))
    print('   lap of the last opener, %s:' % results[1]['name'], sorted(results[1]['P']['last_lap'].items()))
    print('   R* = (8 z_L + 1) m / d_L for the last opener L (exact, nextOpening_gate); in normal-form terms R* = (8 z_L + 1)/(idx_L + e_L).')

    # ---------------------------------------------------------------- 4
    sec('4. Determination of the path: which coordinates fix which part of the outcome')
    print('keys: rs = (residue, sign) by rank; rsq = (residue, sign, quotient) by rank; blk = the blocked readings at R = 1 only, as (rank, idx, sign) or (idx, sign);')
    print('multiset = rsq without rank.  "conf" = number of keys that carry more than one outcome.')
    names = list(results[0]['keys'].keys())
    for n in names:
        print()
        print('key > outcome: %s' % n)
        print('   ' + '   '.join('%s: %d keys, %d conf' % (r['name'], r['keys'][n], r['conf'][n]) for r in results))
    print()
    print('Distinct classes realised (G2) -- (residue, sign) pattern by rank / as a multiset:')
    for r in results:
        print('   %-9s by rank %9d   multiset %9d' % (r['name'], r['distinct_rs'], r['distinct_ms']))
    print('   Upper bounds: 8^6 * 3^6 = %d by rank with three sign values (< 0, = 0, > 0); 8^6 * 2^6 = %d with a two-valued sign (CR uses only e<=0 / e>=0 / always blocked).' % (8 ** 6 * 3 ** 6, 8 ** 6 * 2 ** 6))
    print()
    print('Structure types of the whole path (the sequence of (residue of the opener, lap - quotient), signs omitted / included) as the population grows:')
    for N, n1, n2, mx in structure_growth():
        print('   A(%d): distinct sequences %d (with signs %d), longest path %d moves' % (N, n1, n2, mx))
    print('   [OBS] the count grows with N: the abstraction (residue, lap offset) of the opener sequence does not close on a finite catalogue within these populations.')

    # ---------------------------------------------------------------- 5
    sec('5. Exceptions to "(residue, sign, quotient) determines the whole path": stage and missing coordinate')
    allstage = Counter()
    allcat = Counter()
    for args, r in zip(pops, results):
        ck = r['conf_keys']['rsq>path']
        if not ck:
            print('%-9s no conflict keys' % r['name'])
            continue
        sets_in, pairs = pass2(args, ck)
        print()
        print('--- %s: conflict keys %d, sets inside them %d (of %d)' % (r['name'], len(ck), sets_in, r['total']))
        stage = Counter()
        cat = Counter()
        shown = 0
        for S1, S2_ in pairs:
            k, c, diff, Rs, b1, b2, p1, p2 = explain(S1, S2_)
            stage[k] += 1
            cat[c] += 1
            if shown < 2:
                shown += 1
                print('   S1=%s  S2=%s' % (S1, S2_))
                print('      same prefix of %d moves; at stage %d: %s; states R = %s | %s' % (k - 1, k, c, Rs[0], Rs[1]))
                print('      blockers S1 %s  S2 %s' % (b1, b2))
                for (j, z) in diff:
                    for S, Rk in ((S1, Rs[0]), (S2_, Rs[1])):
                        x = Fr(S[j], S[0]) * Rk
                        print('      rank %d, lap %d, S=%s: rho*R = %s, rho*R - 8*lap = %s  (blocked iff |.|<1)' % (j, z, S, x, x - 8 * z))
        print('   divergence stage histogram (stage 1 = first move):', sorted(stage.items()))
        print('   categories:', dict(cat))
        allstage.update(stage)
        allcat.update(cat)
    print()
    print('All populations: first divergence at stage 1: %d; at stage >= 2: %d.' % (allstage.get(1, 0), sum(v for k, v in allstage.items() if k >= 2)))
    print('Reading [reasoned, exact]: after the first move the state is R1 = (8z+1)/rho_f; whether a reading j is then blocked is |rho_j (8z+1)/rho_f - 8N| < 1,')
    print('an inequality between e_j and e_f (their magnitudes), so the sign classes cannot decide it.  The two sets of a conflict key differ only in such a magnitude.')

    # ---------------------------------------------------------------- 6
    sec('6. Refinement of the sign: does a finite quantisation of e remove the path conflicts?  (full populations)')
    print('   key = (idx, floor(K e)) by rank, outcome = the whole path.  K = 1 means the sign only; bins floor(K e) put e in [0,1/K) with e = 0 (so K=2 is coarser than the sign);')
    print('   K = 720720 separates every e that occurs here (denominators m <= 24 resp. 12).')
    for args_ in ([['A', 16]] if quick else [['A', 24], ['C', 12, 60], ['C', 7, 60]]):
        print('   --- population %s(%s)' % (args_[0], ','.join(map(str, args_[1:]))))
        for K, nk, nc in refinement_test(args_):
            print('      K=%-7d keys %7d, conflict keys %6d' % (K, nk, nc))

    # ---------------------------------------------------------------- 7
    sec('7. Scale: gcd > 1 sets (the same rho) give the same path as the reduced set')
    scale_res = []
    for N in ((16, 18) if quick else (20, 24)):
        p = subprocess.run([os.environ['AW_EXE'], 'S', str(N)], capture_output=True, text=True)
        t = tuple(map(int, p.stderr.split()))
        scale_res.append(t)
        print('   S(%d): gcd-1 sets %d, gcd>1 sets compared with their reduction %d, mismatches %d, oracle mismatches on gcd-1 sets %d  [OBS]' % (N, t[0], t[3], t[4], t[2]))

    # ---------------------------------------------------------------- 8
    NU = 12 if quick else 14
    sec('8. The unit: gate at 1/(8u) for every disparity u, population A(%d)' % NU)
    U = unit_test(NU)
    print('   readings tested %d, reading-table vs direct mismatches %d  [OBS]' % (U['readings'], U['table_mismatch']))
    for k in range(7):
        print('   unit = disparity of rank %d (1 = d_min): sets lonely at R=1 (t = 1/(8u)): %d of %d' % (k + 1, U[('unit rank', k, 'lonely at 1/(8u)')], U['sets']))
    print('   [reasoned] for u > d_min the reading d_min/u < 1 is blocked at R=1, so no set is lonely at 1/(8u).')

    # ---------------------------------------------------------------- 9
    NR = 14 if quick else 24
    sec('9. Rounding rule and |e| <= 1/2: population A(%d), full' % NR)
    RV = rounding_variant_test(NR)
    for v, c in RV.items():
        print('   %-52s sets %d | exact identity (res m + e m mod 8m in [m,7m]) mismatches %d | simple table mismatches (readings) %d | max|e| %.3f | blocked readings %d, of residue not in {0,1,7}: %d, lap formula floor((idx+4)/8) mismatches %d | COMPLETE %d, S2 exceptions %d' % (
            v, c['sets'], c['identity_mismatch'], c['simple_table_reading_mismatch'], c['max_abs_e_x2'] / 2000.0, c['blocked_readings'],
            c['blocked_residue_not_0_1_7'], c['lap_formula_mismatch'], c['complete'], c['S2_exceptions']))
    for S_, idx_, e_ in WILD_EX:
        print('   wild-rounding counterexample to S2: S=%s idx=%s e=%s' % (S_, idx_, [str(x) for x in e_]))
    print('   Sets containing a tie reading rho = k + 1/2 in %s: %d of %d  (the class label can change with the tie rule, loneliness and the cascade cannot).' % (A0['name'], A0['P']['ties'].get('sets_with_tie', 0), A0['total']))

    # ---------------------------------------------------------------- 10
    sec('10. Non-rational test in Q(sqrt 2): d_min = 1, six readings from a pool of numbers k + (sqrt2-1)/2 and k - (sqrt2-1)/3 (k in 2..10,12,15,16,17)')
    npool = 8 if quick else 26
    with Pool(8) as pool:
        parts = pool.map(qs_test, [(c, 8, npool) for c in range(8)])
    q = Counter()
    for part in parts:
        q.update(part)
    print('   all C(%d,6) sets of the pool:' % npool, dict(q))
    print()
    status(results, RV, U, q, tab_exc, tot_exc, scale_res, allstage)
    print()
    print('total seconds %.0f' % (time.time() - t_start))


def status(results, RV, U, q, tab_exc, tot_exc, scale_res, allstage):
    sec('11. Status of every hypothesis: REQUIRED / NOT REQUIRED / UNDECIDED  (each hypothesis was dropped or varied and the statement re-tested; nothing was added)')
    nsets = sum(r['total'] for r in results)
    s2 = Counter()
    p1 = Counter()
    fm = Counter()
    fl = Counter()
    for r in results:
        s2.update(r['P']['S2'])
        p1.update(r['P']['P1'])
        p1.update({'viol_' + k: v for k, v in r['P']['P1same'].items()})
        fm.update(r['P']['FM'])
        fl.update(r['P']['first_lap'])
    blk_conf = sum(r['conf']['blk(idx,sgn)>first'] for r in results)
    rsq_first_conf = sum(r['conf']['rsq>first'] for r in results)
    rsq_path_conf = sum(r['conf']['rsq>path'] for r in results)
    wild = RV['wild: nearest + (-1,0,+1 by rank), |e| up to 3/2']
    up = RV['nearest, tie up']
    dn = RV['nearest, tie down']
    tot_sc = sum(t[3] for t in scale_res)
    mis_sc = sum(t[4] for t in scale_res)
    print('Populations: %d sets in %d populations (section 0 table), plus the Q(sqrt 2) pool and the pairwise exact test; every figure below is an observation on those full populations.' % (nsets, len(results)))
    print()
    print('STATEMENT CR  (R = 1 lonely iff no reading has residue 0, none has residue 1 with e<0, none has residue 7 with e>0)   [OBS: %d exceptions in %d sets; reading-table mismatches %d]' % (tot_exc, nsets, tab_exc))
    print('   integrality of the disparities ............ NOT REQUIRED  (Q(sqrt 2) pool: %d sets, table mismatches %d, lonely<->no-blocker mismatches %d, oracle mismatches %d;' % (
        q['sets'], q['table_mismatch'], q['lonely_iff_noblocker_mismatch'], q['oracle_mismatch']))
    print('                                                scale covariance: %d gcd>1 sets compared with their reduction, %d mismatches; [L] RealCase.clear_shift_iff is stated for real rho)' % (tot_sc, mis_sc))
    print('   gcd of the set = 1 ........................ NOT REQUIRED  (same scale test; the readings rho = d/m do not see the gcd)')
    print('   idx = the NEAREST integer .................. NOT REQUIRED  (the exact identity "clear iff (res*m + e*m) mod 8m in [m,7m]" has %d mismatches under nearest/tie-up, tie-down, floor, ceil and a wild rule)' % (
        sum(RV[v]['identity_mismatch'] for v in RV)))
    print('   |e| <= 1/2 ................................. NOT REQUIRED for the identity;  |e| < 1 is REQUIRED for the three-line table: with |e| up to 3/2 (wild) the table is wrong on %d readings; with floor/ceil (|e|<1) on %d / %d.' % (
        wild['simple_table_reading_mismatch'], RV['floor (e in [0,1))']['simple_table_reading_mismatch'], RV['ceil (e in (-1,0])']['simple_table_reading_mismatch']))
    print('                                                At |e| = 1 the residue-0 entry already fails ([reasoned]: rho = 8q+1 is clear while the table says blocked).')
    print('   the tie rule (rho = k+1/2 up or down) ..... NOT REQUIRED for blocked/lonely/cascade (the blocked set is the same under both, table mismatches %d / %d); it changes the CLASS LABEL only (COMPLETE sets in A(24): %d with tie-up, %d with tie-down).' % (
        up['simple_table_reading_mismatch'], dn['simple_table_reading_mismatch'], up['complete'], dn['complete']))
    print('   d_min as the unit ......................... NOT REQUIRED for the table (units = each of the 7 disparities, %d readings, mismatches %d);' % (U['readings'], U['table_mismatch']))
    print('                                                REQUIRED for "R = 1 can be lonely": for every other unit the lonely count is %d of %d [OBS], because d_min/u < 1 is blocked [reasoned].' % (
        sum(U[('unit rank', k, 'lonely at 1/(8u)')] for k in range(1, 7)), 6 * U['sets']))
    print('   seven distinct disparities ................ NOT REQUIRED [reasoned: CR is a statement about each reading separately]; sets of other sizes were NOT run here.')
    print()
    print('STATEMENT S2  (COMPLETE: R = 1 lonely iff the residue-7 reading has e <= 0)   [OBS: %d exceptions in %d COMPLETE sets]' % (s2['exceptions'], s2['sets']))
    print('   COMPLETE (residues exactly {2..7}) ........ NOT REQUIRED as a hypothesis of the criterion; the exact criterion is CR.  What cannot be dropped: "no residue 0 and no residue 1 with e<0" (REQUIRED):')
    print('                                                e.g. (1,2,3,4,5,6,8) has residue 0, no residue-7 reading, and is not lonely at R=1 (first move to the exit of 8 at lap 1).')
    print('   |e| <= 1/2 with nearest idx ............... |e|<1 REQUIRED, nearest NOT REQUIRED: under the wild rule S2 has %d exceptions in %d COMPLETE sets (example above);' % (wild['S2_exceptions'], wild['complete']))
    print('                                                under nearest / floor / ceil it has %d / %d / %d.' % (up['S2_exceptions'], RV['floor (e in [0,1))']['S2_exceptions'], RV['ceil (e in (-1,0])']['S2_exceptions']))
    print('   integrality, gcd, d_min as unit ........... as for CR.')
    print()
    print('STATEMENT FM  (first move: opener = the blocked reading of largest exit (idx - r + 1)/(idx + e), lap z = floor((idx+4)/8))   [OBS: argmax mismatches %d over %d moved sets; lap mismatches %d; exit-numerator mismatches %d]' % (
        fm['argmax_mismatch'], fm['sets'], fl['rule_mismatch'], fl['exit_numerator_mismatch']))
    print('   exit formula (8z+1 = idx - r + 1, r in {0,+1,-1}) . |e| < 1 REQUIRED: under the wild rule %d of %d blocked readings have a residue outside {0,1,7};' % (wild['blocked_residue_not_0_1_7'], wild['blocked_readings']))
    print('   lap formula floor((idx+4)/8) .............. |e| <= 1/2 NOT REQUIRED (it needs only |idx - 8z| <= 3; %d mismatches under the wild rule, %d under all five).' % (
        wild['lap_formula_mismatch'], sum(RV[v]['lap_formula_mismatch'] for v in RV)))
    print('   the opener is the lowest-rank blocker (P1) ... FALSE as a statement: fails in %d of %d moved sets with a blocker (B(2,20): residue-1 reading at lap 1 against a residue-0 reading at lap 2; C: residue 0/7 pairs).' % (
        p1['sets_with_blocker'] - p1['first_is_lowest_blocker'], p1['sets_with_blocker']))
    print('        It holds in %d of %d sets whose blocked readings share one zone (class-determined), so "one zone" is the hypothesis P1 REQUIRES; with several zones it fails in %d of %d.' % (
        p1['viol_lowest_blocker_opens'], p1['viol_sets_all_blockers_same_lap'], p1['viol_sets_blockers_of_several_laps'] - p1['viol_lowest_blocker_opens_several_laps'], p1['viol_sets_blockers_of_several_laps']))
    print()
    print('STATEMENT DET1  (the blocked readings\' (idx, sign of e) determine the first opener)  -- REFUTED by exact data, not "undecided":')
    print('   conflicting keys (same blocked (rank, idx, sign), different first opener): %d across the populations (all in populations C(m,60) with m >= 4; the two blocked readings lie in different zones); the reason is one inequality' % blk_conf)
    print('   (8 z_a+1)(idx_b+e_b) vs (8 z_b+1)(idx_a+e_a), i.e. a threshold on |e_b| (section 3b prints e_b < 1/9, e_b < 1/18, ...).  Missing coordinate: the MAGNITUDE of e.')
    print('   It held in the populations A and B only because they realise few e values at the relevant pairs; the exact pairwise test (section 3b) has 135 of 623 (idx,sign) cells with two winners.')
    print()
    print('STATEMENT DET2  (residue, sign, quotient by rank determine the whole path / the landing)  -- REFUTED: path-conflict keys %d (A(24): %d, A(28): %d, B(4,10): %d, B(5,8): %d, C populations: %d).' % (
        rsq_path_conf, byname_val(results, 'A(24)'), byname_val(results, 'A(28)'), byname_val(results, 'B(4,10)'), byname_val(results, 'B(5,8)'),
        sum(r['conf']['rsq>path'] for r in results if r['name'].startswith('C('))))
    print('   first divergence of two sets with the same key: stage 1 in %d pairs, stage >= 2 in %d pairs. Reason: after a move the state is R = (8z+1)/rho_f, and whether a later reading is blocked' % (
        allstage.get(1, 0), sum(v for k, v in allstage.items() if k >= 2)))
    print('   is |rho_j R - 8N| < 1, a comparison of the magnitudes e_j and e_f.  Refinement by dyadic bins removes the conflicts only when K exceeds the denominator m (K=8 for m=7, K=16 for m=12): no uniform K [OBS].')
    print('   Quotients: the quotient enters through the lap z = round(idx/8) of an opener and through which blockers share a zone; the data do not test quotients above 7 (C: idx <= 60).')
    print()
    print('STATEMENT G2  (the landing STRUCTURE depends only on a finite class)')
    print('   finite upper bound on (residue, sign) classes by rank: 8^6 * 3^6 (or 8^6 * 2^6)  ... TRUE as a count.')
    print('   first stage: "R = 1 lonely or not, which readings are blocked, their laps and exit numerators" depend on the class and quotient only [OBS, reasoned] ... REQUIRED: |e| < 1.')
    print('   which blocker opens, and every later move ... NOT determined by the class (DET1, DET2).  Number of path structure types (residue of opener, lap offset) grows with N (section 4): UNDECIDED whether it is finite.')
    print('   What the data support instead: the finite part is the blocked set at the current scale; the continuous part is the magnitudes (d_min handles the transition); scale covariance is exact (section 7).')


def byname_val(results, name):
    for r in results:
        if r['name'] == name:
            return r['conf']['rsq>path']
    return 0


if __name__ == '__main__':
    main()

