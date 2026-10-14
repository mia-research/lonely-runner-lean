#!/usr/bin/env python3
"""Quotient-reduced arrangement versus the original: exact data for Fresh/QuotientReduction.lean (task BC).

Rules: 1, 5, 6, 7, 13, 15, 16, 18, 21.   Exact only (integers and Fractions); no floating point; every cascade loop has a move limit
(LIMIT = 100000 in the C kernel, 100000 in the Fraction reference).  No pre-registration, no imports of other frameworks' obligations.
Every count below is [OBS] (a counting tool, never an argument); the Lean statements are in Fresh/QuotientReduction.lean.

Objects.  A set is the 7 disparities of the subject, integers y_0 < ... < y_6 (scale covariant: disparities y_j/Q), m = y_0 = d_min,
rho_j = y_j/m, gate coordinate R = 8 m t.  idx_j = round(rho_j) (tie rho = k + 1/2 goes UP, e = -1/2, as Lean's `round`),
e_j = rho_j - idx_j, ridx_j = (idx_j - 1) mod 8 + 1 in {1..8} (a residue-0 reading is 8, never 0), quo_j = (idx_j - 1) div 8
(idx = ridx + 8 quo), reduced numerator yt_j = y_j - 8 quo_j m (reduced reading rho~_j = ridx_j + e_j in [1/2, 17/2)).
d_min is kept as follows: the coordinate stays R = 8 m t with the ORIGINAL m, the reduced set contains the unit y_0 = m (quo_0 = 0), so its
lonely set is still inside R >= 1; the reduced set may contain readings below 1 (down to 1/2) and equal readings (collisions); both are counted.
Landing = least lonely R >= 1 = the cascade's fixed point from R = 1 (Fresh/Cascade.lean: no overshoot).  The cascade: a reading is blocked at R
iff |rho R - 8 z| < 1 with z = round(rho R / 8); its next opening is (8z+1)/rho; the move goes to the largest.

Populations (all full; no sampling).
  A(N)   : every 7-subset of {1..N} with gcd 1 (the grid_deviation_normal_form_v1.py population), N = 16, 20, 24.
  Q = 3,5: every 7-subset of {Q,...,12Q} whose elements are not all multiples of Q (the real_case_v1.py population; counts 5378824, 231916608).
Kernel cross-checks: (i) an independent least-clear-opening oracle inside the C kernel (the least clear point among the openings (8z+1)m/y_j,
compared with the cascade's landing, for the original AND the reduced set; every set of A(N) and Q=3, every set of Q=5); (ii) an independent
Fraction implementation (this file, section R) reproduces every aggregate of the C kernel on A(16) and A(20); (iii) for Q=5 the integer-instant
agreement is checked over the whole period 8m of a for every set.
Usage: python3 quotient_reduction_v1.py > quotient_reduction_v1.out        (about 6 minutes; needs cc; no background process remains)
"""
import os, sys, subprocess, tempfile, shutil, time
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from collections import Counter

C_SRC = r'''/* Exact integer kernel for quotient_reduction_v1.py (task BC).  No floating point.
   A set is 7 positive integers y_0<...<y_6 (numerators; the disparities are y_j/Q, scale-covariant), m = y_0, rho_j = y_j/m,
   gate coordinate R = 8 m t.  idx_j = round(rho_j) (tie up), e_j = rho_j - idx_j, ridx = (idx-1)%8+1, quo = (idx-1) div 8,
   reduced numerator yt_j = y_j - 8 quo_j m.  A cascade state is R = num/den; reading j is blocked iff |y_j num - 8 z m den| < m den,
   z = floor((y_j num + 4 m den)/(8 m den)); its next opening is (8z+1) m / y_j. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll; typedef __int128 LL;
#define LIMIT 100000
#define NA 520
#define NB 129
static ll gcdl(ll a, ll b){ if(a<0)a=-a; if(b<0)b=-b; while(b){ll t=a%b;a=b;b=t;} return a; }
static ll fl(LL x, LL d){ LL q=x/d; if((x%d!=0)&&((x<0)!=(d<0))) q--; return (ll)q; }
static ll cl(LL x, LL d){ return -fl(-x,d); }
static int cascade(const ll*y,ll m,ll*pn,ll*pd,int*lj,ll*lz){
  ll num=1,den=1; int mv=0; *lj=-1; *lz=0;
  for(;;){
    int best=-1; ll bz=0, bn=0, bd=1;
    for(int j=0;j<7;j++){
      LL xn=(LL)y[j]*num, xd=(LL)m*den;
      ll z=fl(xn+4*xd,8*xd);
      LL dev=xn-(LL)8*z*xd; if(dev<0)dev=-dev;
      if(dev<xd){
        ll nn=(8*z+1)*m, nd=y[j];
        if(best<0 || (LL)nn*bd>(LL)bn*nd){best=j;bz=z;bn=nn;bd=nd;}
      }
    }
    if(best<0){ ll g=gcdl(num,den); *pn=num/g; *pd=den/g; return mv; }
    if(mv>=LIMIT) return -1;
    ll g=gcdl(bn,bd); num=bn/g; den=bd/g; *lj=best; *lz=bz; mv++;
  }
}
static int lonely(const ll*y,ll m,ll num,ll den){
  for(int j=0;j<7;j++){
    LL xn=(LL)y[j]*num, xd=(LL)m*den;
    ll z=fl(xn+4*xd,8*xd);
    LL dev=xn-(LL)8*z*xd; if(dev<0)dev=-dev;
    if(dev<xd) return 0;
  }
  return 1;
}
/* right end of the lonely cell containing R (R lonely): the first zone start (8z-1)m/y_j >= R, minimised over j */
static void cellend(const ll*y,ll m,ll num,ll den,ll*en,ll*ed){
  ll bn=0,bd=0; int have=0;
  for(int j=0;j<7;j++){
    LL xn=(LL)y[j]*num, xd=(LL)m*den;
    ll z=cl(xn+xd,8*xd);
    ll sn=(8*z-1)*m, sd=y[j];
    if(!have || (LL)sn*bd<(LL)bn*sd){bn=sn;bd=sd;have=1;}
  }
  *en=bn;*ed=bd;
}
static int lonelyInt(const ll*y,ll m,ll a){
  for(int j=0;j<7;j++){ ll r=(y[j]*a)%(8*m); if(r<m||r>7*m) return 0; }
  return 1;
}
/* population state */
static ll lo,hi,Qm; static int mode; /* mode 0: A(N) gcd 1;  mode 1: Q population */
static int part=0,nparts=1; static ll cnt3=0; static ll S[7];
static ll oracleEvery=0, chkMax=0; /* chkMax 0 = full period */
/* statistics */
static ll total=0,nofix=0,oraclechk=0,oraclebad=0;
static ll hasOdd=0,hasInt=0,hasEvenOnly=0; static ll firstOdd[NA],firstInt[NA];
static ll mismInt=0,mismFirstOdd=0;
static ll ncollide=0,nbelow1=0,nanyq=0,nallq0=0;
static ll nEq=0,nRlt=0,nRgt=0; static ll catc[2][64];  /* dir,(A,B,inGo,inGr,same) */
static ll vio1=0,vio2=0,vio3=0,vio4=0,vio5=0;
static ll lo1=0,loIntOdd=0,loIntEven=0,loOther=0,loGt7=0,roIs1=0,rrIs1=0;
static ll dispN=0,dispPos=0,dispNeg=0,dispA[NA],dispNh[NB],dispNzero=0,dispIdVio=0,dispEqRed=0,dispRrLo=0,dispRrGo=0;
static ll dminN=0,dminD=1,dmaxN=0,dmaxD=1; static ll dminS[7],dmaxS[7];
static ll rrdisp[NB];
static ll dispFlankRes[9];
static ll maxMoves=0,maxRn=0,maxRd=1; static ll maxRS[7];
static void visit(void){
  ll m=S[0]; total++;
  ll idx[7],en[7],ridx[7],quo[7],yt[7]; ll g=0;
  int anyq=0,collide=0,below=0;
  for(int j=0;j<7;j++){
    ll q=S[j]/m, r=S[j]%m; ll i,e;
    if(2*r<m){i=q;e=r;} else {i=q+1;e=r-m;}
    idx[j]=i;en[j]=e; ridx[j]=(i-1)%8+1; quo[j]=(i-1)/8; /* i>=1 */
    yt[j]=S[j]-8*quo[j]*m; if(quo[j]!=0)anyq=1; g=gcdl(g,quo[j]);
    if(2*yt[j]<m) {} ;
    if(yt[j]<m) below=1;
  }
  for(int j=0;j<7;j++)for(int k=j+1;k<7;k++) if(yt[j]==yt[k]) collide=1;
  if(anyq)nanyq++; else nallq0++;
  ncollide+=collide; nbelow1+=below;
  ll on,od,rn,rd; int lj,rj; ll lz,rz;
  int mo=cascade(S,m,&on,&od,&lj,&lz), mr=cascade(yt,m,&rn,&rd,&rj,&rz);
  if(mo<0||mr<0){nofix++;return;}
  if(mo>maxMoves)maxMoves=mo; if(mr>maxMoves)maxMoves=mr;
  if((LL)on*maxRd>(LL)maxRn*od){maxRn=on;maxRd=od;memcpy(maxRS,S,sizeof S);}
  if(oracleEvery && (total%oracleEvery)==0){
    for(int w=0;w<2;w++){
      const ll*y= w?yt:S; ll tn=w?rn:on, td=w?rd:od; ll bn=-1,bd=1;
      for(int j=0;j<7;j++){
        for(ll z=0;;z++){
          ll cn=(8*z+1)*m, cd=y[j]; /* candidate R=cn/cd, need >=1 */
          if((LL)cn*td>(LL)tn*cd) break;
          if(cn<cd) continue;
          if(lonely(y,m,cn,cd)){ if(bn<0||(LL)cn*bd<(LL)bn*cd){bn=cn;bd=cd;} }
        }
      }
      oraclechk++;
      if(bn<0|| (LL)bn*td!=(LL)tn*bd) oraclebad++;
    }
  }
  /* integer instants */
  ll P=8*m; ll top = chkMax? chkMax : P;
  ll fo=0,fi=0,fro=0;
  for(ll a=1;a<=P;a++){
    int lo_=lonelyInt(S,m,a);
    if(lo_){ if(!fi)fi=a; if((a&1)&&!fo)fo=a; }
    if(a<=top){ int lr=lonelyInt(yt,m,a); if(lr!=lo_) mismInt++; if(lr&&(a&1)&&!fro)fro=a; }
    if(fo && fi && a>top) break;
  }
  if(chkMax==0 || fo<=top){ if(fo!=fro) mismFirstOdd++; }
  if(fo){hasOdd++;firstOdd[fo]++;}
  if(fi){hasInt++;firstInt[fi]++; if(!fo)hasEvenOnly++;}
  /* landings */
  int ro_int=(od==1), rr_int=(rd==1);
  if(on==1&&od==1)roIs1++;
  if(rn==1&&rd==1)rrIs1++;
  if(ro_int){ if(on&1)loIntOdd++; else loIntEven++; } else if((LL)on>(LL)7*od) loGt7++; else loOther++;
  /* is R in the integrality set (1/g)Z : g*R integer */
  int inGo = (g==0) || (((LL)g*on)%od==0);
  int inGr = (g==0) || (((LL)g*rn)%rd==0);
  LL cmp=(LL)rn*od-(LL)on*rd; /* sign of Rr-Ro */
  if(cmp==0){
    nEq++;
  } else {
    int dir = cmp>0; /* 1: Rr>Ro */
    if(dir) nRgt++; else nRlt++;
    int A=lonely(yt,m,on,od), B=lonely(S,m,rn,rd), same;
    ll en_,ed_;
    if(!dir){ cellend(yt,m,rn,rd,&en_,&ed_); same = ((LL)on*ed_<=(LL)en_*od); }
    else { cellend(S,m,on,od,&en_,&ed_); same = ((LL)rn*ed_<=(LL)en_*rd); }
    catc[dir][A*16+B*8+inGo*4+inGr*2+same]++;
    /* Lean consequences */
    if(inGo && dir) vio1++;      /* Ro in G => Rr <= Ro */
    if(inGr && !dir) vio2++;     /* Rr in G => Ro <= Rr */
    if(!anyq) vio3++;
    if(A && dir) vio4++;         /* Ro lonely in red => Rr <= Ro */
    if(B && !dir) vio5++;
  }
  if(fo){ /* common bound: both landings <= first odd lonely integer */
    if((LL)on>(LL)fo*od || (LL)rn>(LL)fo*rd) vio1+=1000000000LL; /* flagged separately below */
  }
  if(!fo){ /* displaced regime: no lonely odd integer instant (period-complete) */
    dispN++;
    ll t=on-2*od; ll kk=cl(t,2*od); ll a=2*kk+1; if(a<1)a=1;
    ll dn=on-a*od, dd=od; /* delta = dn/dd */
    if(dn>0)dispPos++; else dispNeg++;
    if(a<NA)dispA[a]++;
    ll adn=dn<0?-dn:dn;
    if(dminN==0 || (LL)adn*dminD<(LL)dminN*dd){dminN=adn;dminD=dd;memcpy(dminS,S,sizeof S);}
    if((LL)adn*dmaxD>(LL)dmaxN*dd){dmaxN=adn;dmaxD=dd;memcpy(dmaxS,S,sizeof S);}
    if(lj>=0){
      ll N=8*lz+1-a*idx[lj];
      if(N>=-64&&N<=64)dispNh[N+64]++;
      if(N==0)dispNzero++;
      /* identity (R-a) rho = N - a e : (on-a od)/od * y/m == N - a en/m  <=> (on-a od)*y == (N m - a en) od */
      if((LL)(on-a*od)*S[lj] != (LL)(N*m-a*en[lj])*od) dispIdVio++;
      dispFlankRes[idx[lj]%8]++;
    }
    if(cmp==0)dispEqRed++; else if(cmp<0)dispRrLo++; else dispRrGo++;
  }
}
static void rec(int pos,ll start){
  if(pos==3){ ll c=cnt3++; if(c%nparts!=part) return; }
  if(pos==7){
    if(mode==0){ ll g=0; for(int j=0;j<7;j++)g=gcdl(g,S[j]); if(g!=1)return; }
    else { int all=1; for(int j=0;j<7;j++) if(S[j]%Qm){all=0;break;} if(all)return; }
    visit(); return; }
  for(ll v=start; v<=hi-(6-pos); v++){S[pos]=v; rec(pos+1,v+1);}
}
static void pa(const char*name,ll*arr,int n){ printf("%s",name); for(int i=0;i<n;i++) if(arr[i]) printf(" %d:%lld",i,arr[i]); printf("\n"); }
int main(int argc,char**argv){
  /* usage: qr A N part nparts oracleEvery chkMax | qr Q Qm part nparts oracleEvery chkMax */
  mode = argv[1][0]=='A'?0:1;
  if(mode==0){ lo=1; hi=atoll(argv[2]); Qm=1; } else { Qm=atoll(argv[2]); lo=Qm; hi=12*Qm; }
  part=atoi(argv[3]); nparts=atoi(argv[4]); oracleEvery=atoll(argv[5]); chkMax=atoll(argv[6]);
  rec(0,lo);
  printf("total %lld\nnofix %lld\noraclechk %lld\noraclebad %lld\nhasOdd %lld\nhasInt %lld\nhasEvenOnly %lld\n",total,nofix,oraclechk,oraclebad,hasOdd,hasInt,hasEvenOnly);
  printf("mismInt %lld\nmismFirstOdd %lld\nncollide %lld\nnbelow1 %lld\nnanyq %lld\nnallq0 %lld\n",mismInt,mismFirstOdd,ncollide,nbelow1,nanyq,nallq0);
  printf("nEq %lld\nnRlt %lld\nnRgt %lld\n",nEq,nRlt,nRgt);
  printf("vio_RoInG_RrGt %lld\nvio_RrInG_RoGt %lld\nvio_allq0_differ %lld\nvio_RoLonelyRed_RrGt %lld\nvio_RrLonelyOrig_RoGt %lld\n",vio1%1000000000LL,vio2,vio3,vio4,vio5);
  printf("vio_landing_above_firstodd %lld\n",vio1/1000000000LL);
  printf("roIs1 %lld\nrrIs1 %lld\nloIntOdd %lld\nloIntEven %lld\nloOther %lld\nloGt7 %lld\n",roIs1,rrIs1,loIntOdd,loIntEven,loOther,loGt7);
  printf("dispN %lld\ndispPos %lld\ndispNeg %lld\ndispNzero %lld\ndispIdVio %lld\ndispEqRed %lld\ndispRrLo %lld\ndispRrGo %lld\n",dispN,dispPos,dispNeg,dispNzero,dispIdVio,dispEqRed,dispRrLo,dispRrGo);
  printf("dmin %lld/%lld :",dminN,dminD); for(int j=0;j<7;j++)printf(" %lld",dminS[j]); printf("\n");
  printf("dmax %lld/%lld :",dmaxN,dmaxD); for(int j=0;j<7;j++)printf(" %lld",dmaxS[j]); printf("\n");
  printf("maxRo %lld/%lld :",maxRn,maxRd); for(int j=0;j<7;j++)printf(" %lld",maxRS[j]); printf("\n");
  printf("maxMoves %lld\n",maxMoves);
  pa("firstOdd",firstOdd,NA); pa("firstInt",firstInt,NA); pa("dispA",dispA,NA); pa("dispN",dispNh,NB); pa("dispFlankRes",dispFlankRes,9);
  for(int d=0;d<2;d++){ printf("cat%d",d); for(int k=0;k<64;k++) if(catc[d][k]) printf(" %d:%lld",k,catc[d][k]); printf("\n"); }
  return 0; }
'''

EXE = None
WORK = None

def build():
    global EXE, WORK
    WORK = tempfile.mkdtemp(prefix='qr_kernel_')
    src = os.path.join(WORK, 'qr.c')
    open(src, 'w').write(C_SRC)
    EXE = os.path.join(WORK, 'qr')
    subprocess.check_call(['cc', '-O2', '-o', EXE, src])

def parse_hist(rest):
    d = {}
    for tok in rest.split():
        k, v = tok.split(':')
        d[int(k)] = int(v)
    return d

# the kernel prints the scalar `dispN` (a count) and a histogram line that also starts with `dispN`: the histogram is renamed
def merge_fix(outs):
    outs2 = []
    for out in outs:
        lines = out.strip().split('\n')
        new = []
        for line in lines:
            if (line.startswith('dispN ') and ':' in line) or line.strip() == 'dispN':
                line = 'dispNhist ' + line[len('dispN '):]
            new.append(line)
        outs2.append('\n'.join(new))
    return merge_h(outs2)

def merge_h(outs):
    M = {}
    for out in outs:
        for line in out.strip().split('\n'):
            key, _, rest = line.partition(' ')
            if key in ('firstOdd', 'firstInt', 'dispA', 'dispNhist', 'dispFlankRes', 'cat0', 'cat1'):
                tgt = M.setdefault(key, Counter())
                if rest.strip():
                    for k, v in parse_hist(rest).items(): tgt[k] += v
            elif key in ('dmin', 'dmax', 'maxRo'):
                frac, _, st = rest.partition(' :')
                a, b = frac.split('/')
                val = F(int(a), int(b))
                st = tuple(int(x) for x in st.split())
                cur = M.get(key)
                if key == 'dmin':
                    if val != 0 and (cur is None or val < cur[0]): M[key] = (val, st)
                else:
                    if cur is None or val > cur[0]: M[key] = (val, st)
            else:
                M[key] = M.get(key, 0) + int(rest)
    return M

def run_pop2(kind, par, nparts, oracle_every, chk):
    procs = [subprocess.Popen([EXE, kind, str(par), str(p), str(nparts), str(oracle_every), str(chk)], stdout=subprocess.PIPE, text=True)
             for p in range(nparts)]
    outs = [pr.communicate()[0] for pr in procs]
    for pr in procs: assert pr.returncode == 0
    return merge_fix(outs)

# ---------------------------------------------------------------------------------------------------------------
# Section R: independent Fraction reference (same aggregates as the kernel).
# ---------------------------------------------------------------------------------------------------------------
LIMIT = 100000

def f_cascade(ys, m):
    R = F(1); last = None
    for _ in range(LIMIT):
        best = None
        for j, y in enumerate(ys):
            x = F(y, m) * R
            z = (x / 8 + F(1, 2)).__floor__()
            if abs(x - 8 * z) < 1:
                nx = F(8 * z + 1) * m / y
                if best is None or nx > best[0]: best = (nx, j, z)
        if best is None: return R, last
        R = best[0]; last = (best[1], best[2])
    return None, None

def f_blocked(ys, m, R):
    return [j for j, y in enumerate(ys) if abs(F(y, m) * R - 8 * ((F(y, m) * R / 8 + F(1, 2)).__floor__())) < 1]

def f_cellend(ys, m, R):
    best = None
    for y in ys:
        x = F(y, m) * R
        z = ((x + 1) / 8).__ceil__()
        s = F(8 * z - 1) * m / y
        if best is None or s < best: best = s
    return best

def f_win_int(ys, m, a):
    for y in ys:
        x = F(y, m) * a
        r = x - 8 * (x / 8).__floor__()
        if not (1 <= r <= 7): return False
    return True

def f_feats(S, m):
    out = []
    for y in S:
        rho = F(y, m)
        idx = (rho + F(1, 2)).__floor__()
        e = rho - idx
        out.append((idx, e, (idx - 1) % 8 + 1, (idx - 1) // 8))
    return out

def reference(N):
    A = Counter(); H = {k: Counter() for k in ('firstOdd', 'firstInt', 'dispA', 'dispNhist', 'dispFlankRes', 'cat0', 'cat1')}
    dmin = None; dmax = None
    for S in combinations(range(1, N + 1), 7):
        g = 0
        for y in S: g = gcd(g, y)
        if g != 1: continue
        m = S[0]; A['total'] += 1
        fs = f_feats(S, m); qs = [f[3] for f in fs]
        yt = [y - 8 * f[3] * m for y, f in zip(S, fs)]
        G = 0
        for q in qs: G = gcd(G, q)
        if any(qs): A['nanyq'] += 1
        else: A['nallq0'] += 1
        if len(set(yt)) < 7: A['ncollide'] += 1
        if min(yt) < m: A['nbelow1'] += 1
        Ro, lo_ = f_cascade(S, m); Rr, lr = f_cascade(yt, m)
        fo = fi = None
        for a in range(1, 8 * m + 1):
            if f_win_int(S, m, a):
                if fi is None: fi = a
                if a % 2 == 1 and fo is None: fo = a
            if fi is not None and fo is not None: break
        if fo: A['hasOdd'] += 1; H['firstOdd'][fo] += 1
        if fi:
            A['hasInt'] += 1; H['firstInt'][fi] += 1
            if not fo: A['hasEvenOnly'] += 1
        if Ro == 1: A['roIs1'] += 1
        if Rr == 1: A['rrIs1'] += 1
        if Ro.denominator == 1:
            if Ro.numerator % 2: A['loIntOdd'] += 1
            else: A['loIntEven'] += 1
        elif Ro > 7: A['loGt7'] += 1
        else: A['loOther'] += 1
        inGo = (G == 0) or (G * Ro).denominator == 1
        inGr = (G == 0) or (G * Rr).denominator == 1
        if Ro == Rr: A['nEq'] += 1
        else:
            d = 1 if Rr > Ro else 0
            A['nRgt' if d else 'nRlt'] += 1
            Al = not f_blocked(yt, m, Ro); Bl = not f_blocked(S, m, Rr)
            if not d: same = Ro <= f_cellend(yt, m, Rr)
            else: same = Rr <= f_cellend(S, m, Ro)
            H['cat%d' % d][Al * 16 + Bl * 8 + inGo * 4 + inGr * 2 + same] += 1
            if inGo and d: A['vio_RoInG_RrGt'] += 1
            if inGr and not d: A['vio_RrInG_RoGt'] += 1
            if not any(qs): A['vio_allq0_differ'] += 1
            if Al and d: A['vio_RoLonelyRed_RrGt'] += 1
            if Bl and not d: A['vio_RrLonelyOrig_RoGt'] += 1
        if fo and (Ro > fo or Rr > fo): A['vio_landing_above_firstodd'] += 1
        if not fo:
            A['dispN'] += 1
            kk = ((Ro - 2) / 2).__ceil__()
            a = 2 * kk + 1
            if a < 1: a = 1
            dl = Ro - a
            if dl > 0: A['dispPos'] += 1
            else: A['dispNeg'] += 1
            H['dispA'][a] += 1
            ad = abs(dl)
            if ad != 0 and (dmin is None or ad < dmin[0]): dmin = (ad, S)
            if dmax is None or ad > dmax[0]: dmax = (ad, S)
            j, z = lo_
            Nn = 8 * z + 1 - a * fs[j][0]
            H['dispNhist'][Nn + 64] += 1
            if Nn == 0: A['dispNzero'] += 1
            rho = F(S[j], m)
            if (Ro - a) * rho != Nn - a * fs[j][1]: A['dispIdVio'] += 1
            H['dispFlankRes'][fs[j][0] % 8] += 1
            if Ro == Rr: A['dispEqRed'] += 1
            elif Rr < Ro: A['dispRrLo'] += 1
            else: A['dispRrGo'] += 1
    return A, H, dmin, dmax

def compare(label, M, A, H, dmin, dmax):
    bad = []
    for k, v in A.items():
        if M.get(k, 0) != v: bad.append((k, M.get(k, 0), v))
    for k in ('hasOdd', 'hasInt', 'nEq', 'nRlt', 'nRgt', 'dispN', 'total', 'roIs1', 'rrIs1', 'hasEvenOnly', 'loIntOdd', 'loIntEven', 'loOther',
              'loGt7', 'ncollide', 'nbelow1', 'nanyq', 'nallq0', 'dispPos', 'dispNeg', 'dispNzero'):
        if M.get(k, 0) != A.get(k, 0): bad.append((k, M.get(k, 0), A.get(k, 0)))
    for k, c in H.items():
        if dict(M[k]) != dict(c): bad.append((k, 'hist differs'))
    if M['dmin'][0] != dmin[0] or M['dmax'][0] != dmax[0]: bad.append(('dmin/dmax', M['dmin'][0], dmin[0], M['dmax'][0], dmax[0]))
    print('REFERENCE vs KERNEL on %s: %s' % (label, 'identical on every aggregate (%d scalar keys, %d histograms, dmin, dmax)' % (len(A), len(H)) if not bad else 'DIFFERENCES %s' % bad[:6]))

# ---------------------------------------------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------------------------------------------
def pct(a, b):
    return '%d/%d = %.3f%%' % (a, b, 100.0 * a / b) if b else '%d/0' % a

def report(label, M):
    T = M['total']
    print('POPULATION %s: sets %d (sets on which a cascade hit the move limit: %d)' % (label, T, M['nofix']))
    print('  oracle (least clear opening) disagreements with the cascade landing: %d of %d checks (original and reduced)' % (M['oraclebad'], M['oraclechk']))
    print('  reduced set: some reading below the unit %s; two reduced readings equal %s; no quotient at all (reduced = original) %s' % (
        pct(M['nbelow1'], T), pct(M['ncollide'], T), pct(M['nallq0'], T)))
    print('  (2) lonely ODD integer instant R = a (period-complete: a in 1..8m): %s;  some integer instant %s;  even-only %d' % (
        pct(M['hasOdd'], T), pct(M['hasInt'], T), M['hasEvenOnly']))
    fo = M['firstOdd']
    small = sum(fo[a] for a in (1, 3, 5, 7))
    print('      least lonely odd a: %s' % ' '.join('%d:%d' % (a, fo[a]) for a in sorted(fo)))
    print('      a in {1,3,5,7} only: %s (real_case_v1.out "some odd a works"); a >= 9 adds %d' % (pct(small, T), M['hasOdd'] - small))
    fi = M['firstInt']
    print('      least lonely integer a (any parity): %s' % ' '.join('%d:%d' % (a, fi[a]) for a in sorted(fi)))
    print('      original vs reduced lonely status at integer a over a = 1..%s: disagreements %d;  least lonely odd a differs: %d' % (
        'min(8m, check limit)', M['mismInt'], M['mismFirstOdd']))
    print('  landings (least lonely R >= 1): original R* = 1: %s;  R* an odd integer %d, an even integer %d, non-integer %d, > 7: %d' % (
        pct(M['roIs1'], T), M['loIntOdd'], M['loIntEven'], M['loOther'], M['loGt7']))
    print('      max original landing %s at S = %s' % (M['maxRo'][0], M['maxRo'][1]))
    print('  (3) original vs reduced landing: equal %s;  reduced < original %d;  reduced > original %d' % (pct(M['nEq'], T), M['nRlt'], M['nRgt']))
    print('      consequences of the Lean theorems (violations must be 0): Ro in (1/g)Z and Rr>Ro: %d;  Rr in (1/g)Z and Ro>Rr: %d;  no quotient and landings differ: %d;'
          % (M['vio_RoInG_RrGt'], M['vio_RrInG_RoGt'], M['vio_allq0_differ']))
    print('        Ro lonely for reduced and Rr>Ro: %d;  Rr lonely for original and Ro>Rr: %d;  a landing above the least lonely odd integer: %d'
          % (M['vio_RoLonelyRed_RrGt'], M['vio_RrLonelyOrig_RoGt'], M['vio_landing_above_firstodd']))
    print('      differing sets by (A = Ro lonely for reduced, B = Rr lonely for original, Ro in (1/g)Z, Rr in (1/g)Z, same cell of the arrangement whose landing is smaller):')
    for d, name in ((0, 'Rr < Ro'), (1, 'Rr > Ro')):
        for k, v in sorted(M['cat%d' % d].items()):
            print('        %s: A=%d B=%d Ro_inG=%d Rr_inG=%d same_cell=%d : %d' % (name, k >> 4 & 1, k >> 3 & 1, k >> 2 & 1, k >> 1 & 1, k & 1, v))
    D = M['dispN']
    print('  (2) DISPLACED regime = no lonely odd integer instant: %s' % pct(D, T))
    if D:
        print('      nearest odd integer a to the original landing R*: %s' % ' '.join('%d:%d' % (a, c) for a, c in sorted(M['dispA'].items())))
        print('      sign of R* - a: positive %d, negative %d (zero impossible: R* = a would be a lonely odd integer)' % (M['dispPos'], M['dispNeg']))
        print('      min |R* - a| = %s at S = %s ;  max |R* - a| = %s at S = %s' % (M['dmin'][0], M['dmin'][1], M['dmax'][0], M['dmax'][1]))
        print('      cascade terms: R* = (8z+1)/rho_j for the last mover j; (R*-a) rho_j = Ngrid - a e_j with Ngrid = 8z+1 - a idx_j (integer):')
        print('        histogram of Ngrid: %s' % ' '.join('%d:%d' % (n - 64, c) for n, c in sorted(M['dispNhist'].items())))
        print('        Ngrid = 0 (pure deviation displacement -a e_j/rho_j): %d;  identity (R*-a) rho_j = Ngrid - a e_j violated: %d' % (M['dispNzero'], M['dispIdVio']))
        print('        idx_j mod 8 of the last mover: %s' % ' '.join('%d:%d' % (a, c) for a, c in sorted(M['dispFlankRes'].items())))
        print('      reduced landing vs original in the displaced regime: equal %d, reduced smaller %d, reduced larger %d' % (M['dispEqRed'], M['dispRrLo'], M['dispRrGo']))
    print()

# ---------------------------------------------------------------------------------------------------------------
# Exact examples with reasons (Fractions)
# ---------------------------------------------------------------------------------------------------------------
def explain(S):
    m = S[0]
    fs = f_feats(S, m); qs = [f[3] for f in fs]
    yt = [y - 8 * f[3] * m for y, f in zip(S, fs)]
    Ro, lo_ = f_cascade(S, m); Rr, lr = f_cascade(yt, m)
    print('  S = %s  m = %d' % (S, m))
    print('    idx = %s  e = %s  ridx = %s  quo = %s  reduced = %s' % ([f[0] for f in fs], [str(f[1]) for f in fs], [f[2] for f in fs], qs, yt))
    print('    landing original Ro = %s (last mover reading %s, lap z=%s);  landing reduced Rr = %s (last mover %s, z=%s)' % (
        Ro, S[lo_[0]] if lo_ else None, lo_[1] if lo_ else None, Rr, yt[lr[0]] if lr else None, lr[1] if lr else None))
    for R, nm in ((Rr, 'Rr'), (Ro, 'Ro')):
        rows = []
        for j in range(7):
            sh = (F(qs[j]) * R) % 1   # fractional part of quo R
            red = F(yt[j], m) * R
            orig = F(S[j], m) * R
            rows.append('%d:{qR}=%s red=%s orig=%s' % (S[j], sh, red % 8, orig % 8))
        print('    at %s = %s: blocked in original %s, blocked in reduced %s ; per reading (j: {quo R}, reduced reading mod 8, original reading mod 8): %s' % (
            nm, R, [S[j] for j in f_blocked(S, m, R)], [S[j] for j in f_blocked(yt, m, R)], '; '.join(rows)))

def formula_check(N):
    """win_orig_iff_fract: lonely_orig(R) iff every (reduced reading + 8 {quo R}) mod 8 in [1,7], at nine R per set, every set of A(N)."""
    tested = 0; bad = 0
    pts = [F(1, 2), F(9, 8), F(4, 3), F(3, 2), F(9, 2), F(53, 16), F(17, 3), F(7, 5), F(11, 4)]
    for S in combinations(range(1, N + 1), 7):
        g = 0
        for y in S: g = gcd(g, y)
        if g != 1: continue
        m = S[0]; fs = f_feats(S, m); qs = [f[3] for f in fs]
        yt = [y - 8 * f[3] * m for y, f in zip(S, fs)]
        Ro, _ = f_cascade(S, m); Rr, _ = f_cascade(yt, m)
        for R in pts + [Ro, Rr]:
            direct = not f_blocked(S, m, R)
            ok = True
            for j in range(7):
                x = F(yt[j], m) * R + 8 * ((F(qs[j]) * R) % 1)
                r = x - 8 * (x / 8).__floor__()
                if not (1 <= r <= 7): ok = False; break
            tested += 1
            if ok != direct: bad += 1
    print('FORMULA lonely_orig(R) <=> all (reduced reading + 8 {quo R}) mod 8 in [1,7] (Lean lonelyR_iff_shifted): %d tests on A(%d), %d disagreements' % (tested, N, bad))

def window_check(N):
    """lonelyR_window_iff: with |e a| <= 1 for all readings the residue-class criterion equals the exact status; without the window it can fail."""
    holds = fails = fail_window_bad = fail_window_total = 0
    nexact2 = [0, 0]
    for S in combinations(range(1, N + 1), 7):
        g = 0
        for y in S: g = gcd(g, y)
        if g != 1: continue
        m = S[0]; fs = f_feats(S, m)
        for a in range(1, 8 * m + 1, 2):
            win = all(abs(f[1] * a) <= 1 for f in fs)
            crit = True
            for f in fs:
                r = (f[2] * a) % 8; e = f[1]
                if r == 0 and not abs(e * a) >= 1: crit = False
                if r == 1 and not e >= 0: crit = False
                if r == 7 and not e <= 0: crit = False
            exact = f_win_int(S, m, a)
            ex2 = all(1 <= ((F((f[2] * a) % 8) + f[1] * a) % 8) <= 7 for f in fs)
            nexact2[0] += 1
            if ex2 != exact: nexact2[1] += 1
            if win:
                holds += 1
                if crit != exact: fails += 1
            else:
                fail_window_total += 1
                if crit != exact: fail_window_bad += 1
    print('WINDOW (odd a, A(%d)): window holds in %d (set,a) pairs, criterion vs exact disagreements %d;  window fails in %d pairs, criterion vs exact disagreements %d' % (
        N, holds, fails, fail_window_total, fail_window_bad))
    print('EXACT CRITERION (odd a, A(%d); Lean lonelyR_int_iff): lonely at R = a iff every (r_j + e_j a) mod 8 in [1,7], r_j = (ridx_j a) mod 8: %d pairs, %d disagreements' % (N, nexact2[0], nexact2[1]))

if __name__ == '__main__':
    t0 = time.time()
    build()
    print('QUOTIENT-REDUCED ARRANGEMENT, exact data (task BC).  Kernel source embedded; compiled with cc at run time.')
    print()
    pops = []
    for N in (16, 20, 24):
        M = run_pop2('A', N, 1, 1, 0)
        report('A(%d): 7-subsets of {1..%d}, gcd 1' % (N, N), M)
        pops.append((N, M))
    M3 = run_pop2('Q', 3, 10, 1, 0)
    report('Q = 3: 7-subsets of {3..36}, not all multiples of 3', M3)
    M5 = run_pop2('Q', 5, 10, 1, 0)
    report('Q = 5: 7-subsets of {5..60}, not all multiples of 5', M5)
    print('SECTION R (independent Fraction reference)')
    for N, M in pops[:2]:
        A, H, dmin, dmax = reference(N)
        compare('A(%d)' % N, M, A, H, dmin, dmax)
    formula_check(16)
    window_check(16)
    print()
    print('EXACT EXAMPLES WITH REASONS')
    print(' (a) both landings are the first opening of a residue-0 reading; the original reading 16 = 8*2 sits two laps up, the reduced reading 8 one lap:')
    explain((1, 2, 3, 4, 5, 6, 16))
    print(' (b) reduced landing is lonely for the original only if every reading with a quotient has quo R an integer; here quo R = 9/8 is not:')
    explain((1, 2, 3, 4, 5, 8, 14))
    print(' (c) original landing below the reduced one:')
    explain((1, 2, 3, 4, 5, 14, 16))
    print(' (d) the smallest displacement |R* - a| in the Q = 5 population (m = 7), a set with no lonely odd integer instant:')
    explain((7, 13, 24, 32, 41, 46, 58))
    print(' (d2) the family (1,2,3,4,5,6,8k): landing 1 + 1/(8k), displacement 1/(8k) from a = 1 (Lean landing_family):')
    for k in (1, 2, 5, 10):
        S = (1, 2, 3, 4, 5, 6, 8 * k)
        Ro, _ = f_cascade(S, 1)
        print('    k = %d: S = %s  landing %s = 1 + 1/%d : %s' % (k, S, Ro, 8 * k, Ro == 1 + F(1, 8 * k)))
    print(' (e) reduced reading below the unit (m = 2, y = 17: rho = 8.5, idx = 9, e = -1/2, ridx = 1, quo = 1, reduced 1 = m/2):')
    explain((2, 3, 4, 5, 6, 7, 17))
    print('elapsed %.1f s' % (time.time() - t0))
    shutil.rmtree(WORK, ignore_errors=True)
