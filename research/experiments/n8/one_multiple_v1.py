#!/usr/bin/env python3
"""one_multiple_v1.py  --  Task AR (exact data, all grades [OBS]).

Statement under test.  D = D' u {8c1 [,8c2]} integers, D' = set of positive integers not divisible by 8.
LONELY instant: t > 0 with distInt(d t) >= 1/8 for every d in D.  Integer speeds => the lonely set is 1-periodic in t
and t = 1 is not lonely, so a lonely instant exists iff one lies in (0,1).  With s = 8t = a + eta (a = floor).

Two independent exact tests, integers only (C kernel, int64):
  (CASC)  the cascade of Framework.IsMove from t0 = 1/(8 d_min): move to the largest next opening among runners in
          the way; stop when none in the way (lonely) or when t >= 1 (no lonely instant).
  (OPEN)  least clear opening: every lonely component starts at a left end (8k+1)/(8d) of some runner d, so the least
          lonely t > 0 is the least t among the candidates (8k+1)/(8d), 0<=k<d, at which all runners are clear.
These must give the same t; any disagreement is counted and printed.

Populations are FULL enumerations (stated per block).  No sampling, no floats.  Counts are observations only.
"""
import subprocess, sys, os, itertools, math, time, tempfile
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
SCR = "/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/048fab6c-3e10-4491-a999-fe7558a09487/scratchpad/ar"
os.makedirs(SCR, exist_ok=True)

C_SRC = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static ll cdiv(ll a, ll b){ /* ceil(a/b), b>0 */ ll q=a/b; if (a%b!=0 && a>0) q++; return q; }

#define MAXC 160
#define NMAX 12
static char *cname[MAXC]; static ll cnt[MAXC]; static char cex[MAXC][160]; static int ncnt=0;
static char *mname[MAXC]; static ll mxv[MAXC]; static char mex[MAXC][160]; static int nmx=0;
static int reg(char *n){ cname[ncnt]=n; cex[ncnt][0]=0; return ncnt++; }
static int regm(char *n){ mname[nmx]=n; mex[nmx][0]=0; mxv[nmx]=-1; return nmx++; }

static int mD; static int R; /* number of multiples 0,1,2 */
static int N, CM;            /* N entry bound for D'; CM bound for c */
static int DETAIL;
static int allowed[400], nal;
static int Dp[NMAX];
static ll idx_counter=0; static int W=1, WK=0;

static char exbuf[160];
static void mkex(int c1, int c2){
  char *p=exbuf; p+=sprintf(p,"D'=");
  for(int i=0;i<mD;i++) p+=sprintf(p,"%03d,",Dp[i]);
  p+=sprintf(p," c=%04d",c1); if(c2) p+=sprintf(p,",%04d",c2);
}
#define HIT(k,c1,c2) do{ cnt[k]++; if(!cex[k][0]){ mkex(c1,c2); strcpy(cex[k],exbuf);} }while(0)
#define HITX(k,c1,c2,extra) do{ cnt[k]++; if(!cex[k][0]){ mkex(c1,c2); strcpy(cex[k],exbuf); sprintf(cex[k]+strlen(cex[k])," %s",extra);} }while(0)

/* counters */
enum { K_PAIRS, K_FAIL, K_MISMATCH, K_GCD_GT1, K_GCD_GT1_FAIL, K_GCD1, K_GCD1_FAIL,
  K_OP_MULT, K_OP_DP, K_OP_BOTH, K_M1, K_MINT, K_NONINT,
  K_LA0, K_LA1, K_LA2, K_LA3, K_LA4, K_LA5, K_LA6, K_LA7,
  K_A1_EXISTS, K_A1_NONE, K_LAND_EQ_A1, K_LAND_EQ_A0, K_LAND_RES_OK, K_LAND_HAS0, K_LAND_HAS7,
  K_F1_ANY, K_F1_ANY_FAIL, K_F1_A1, K_F1_A1_FAIL, K_FM_ANY_FAIL, K_FMULT_AT_LANDINGA_FAIL,
  K_G_ANY_FAIL, K_BIG_EMPTY, K_LAND_IN_BIG, K_LAND_NOTIN_BIG, K_LAND_EQ_MINBIG, K_LAND_NEQ_MINBIG,
  K_BIGLONE_BB, K_BIGLONE_BN, K_BIGLONE_NB, K_BIGLONE_NN, K_BIGEMPTY_LONE,
  K_J0, K_J1, K_J2, K_J3to7, K_J8to15, K_J16p, K_LAND_EQ_MINLONE_A,
  K_MULTIPLE_FIRST_GE, K_LAND_A_IS_FIRSTRES, K_LAP0, K_LAP1, K_LAP2p, K_NEEDS_RES07, K_DEXC, K_SUFF_A1, K_SUFF_NOT_F1, K_F1_NOT_SUFF, K_PX_MISMATCH_UNIT, K_PX_MISMATCH_LAND, K_LAND_LT_APOS, K_LAND_EQ_APOS, K_LAND_GT_APOS, K_BIGAPOS, K_BIGAPOS_LAND_NEQ_APOS, K_NOAPOS, K_SKIP0, K_SKIP1, K_SKIP2, K_SKIP3p, K_SKIPPED_BIG, K_DP_ZEROLEN };
static int K[160];
enum { M_MOVES, M_J, M_MMIN, M_LAP, M_DPLAND, M_MMINA1, M_C0, M_RATIO };
static int MX[16];

static int clearD(int nd, const ll *ds, ll num, ll den){
  for(int i=0;i<nd;i++){ ll r=(ds[i]*num)%den; ll m = r<den-r?r:den-r; if(8*m<den) return 0; }
  return 1;
}

/* cascade: returns 1 and t=(num,den) if lonely, 0 if fails; moves */
static int cascade(int nd, const ll *ds, ll *tn, ll *td, int *moves){
  ll dmin=ds[0]; for(int i=1;i<nd;i++) if(ds[i]<dmin) dmin=ds[i];
  ll num=1, den=8*dmin; int mv=0;
  for(;;){
    ll bn=0, bd=1; int any=0;
    for(int i=0;i<nd;i++){
      ll d=ds[i]; ll r=(d*num)%den; ll m = r<den-r?r:den-r;
      if(8*m<den){
        ll q = cdiv(8*d*num-den, 8*den);
        ll nn=8*q+1, nd2=8*d; /* next opening nn/nd2 */
        if(!any || nn*bd > bn*nd2){ bn=nn; bd=nd2; any=1; }
      }
    }
    if(!any){ *tn=num; *td=den; *moves=mv; return 1; }
    num=bn; den=bd; mv++;
    if(num>=den){ *tn=num; *td=den; *moves=mv; return 0; }
  }
}

/* least lonely via candidate left ends; returns 1 and t, and mask of a's that contain a lonely point */
static int openmin(int nd, const ll *ds, ll *tn, ll *td, int *mask){
  int found=0; ll bn=0,bd=1; int mk=0;
  for(int i=0;i<nd;i++){
    ll d=ds[i];
    for(ll k=0;k<d;k++){
      ll num=8*k+1, den=8*d;
      if(clearD(nd,ds,num,den)){
        int a=(int)(8*num/den); mk|=1<<a;
        if(!found || num*bd < bn*den){ bn=num; bd=den; found=1; }
        break; /* later k of the same runner are later in time, but other a-bits needed: handled below */
      }
    }
  }
  /* full a-mask: need every candidate, not only the first of each runner */
  if(DETAIL>=2){
    mk=0;
    for(int i=0;i<nd;i++){ ll d=ds[i];
      for(ll k=0;k<d;k++){ ll num=8*k+1, den=8*d;
        if(clearD(nd,ds,num,den)) mk|=1<<(int)(8*num/den); } }
  }
  *mask=mk; if(found){ *tn=bn; *td=bd; } return found;
}

/* cells of D'-compatible set in [a,a+1] (s units): longest cell length as fraction p/q */
typedef struct { ll lo_n, lo_d, hi_n, hi_d; } iv;
static ll Lp[8], Lq[8];
static iv CE[8][256]; static int NCE[8];
static void cells(void){
  for(int a=0;a<8;a++){
    iv cur[256]; int nc=1; cur[0].lo_n=a; cur[0].lo_d=1; cur[0].hi_n=a+1; cur[0].hi_d=1;
    for(int j=0;j<mD && nc>0;j++){
      ll d=Dp[j]; iv nw[256]; int nn=0;
      for(int i=0;i<nc;i++){
        ll klo = (cur[i].lo_n*d)/(8*cur[i].lo_d) - 1; if(klo<0) klo=0;
        ll khi = (cur[i].hi_n*d)/(8*cur[i].hi_d) + 1;
        for(ll k=klo;k<=khi;k++){
          /* [ (8k+1)/d , (8k+7)/d ] */
          ll ln=8*k+1, hn=8*k+7;
          iv x;
          /* lo = max(cur.lo, ln/d) */
          if (cur[i].lo_n*d >= ln*cur[i].lo_d){ x.lo_n=cur[i].lo_n; x.lo_d=cur[i].lo_d; } else { x.lo_n=ln; x.lo_d=d; }
          if (cur[i].hi_n*d <= hn*cur[i].hi_d){ x.hi_n=cur[i].hi_n; x.hi_d=cur[i].hi_d; } else { x.hi_n=hn; x.hi_d=d; }
          if (x.lo_n*x.hi_d <= x.hi_n*x.lo_d){ if(nn<256) nw[nn++]=x; }
        }
      }
      nc=nn; memcpy(cur,nw,sizeof(iv)*nn);
    }
    NCE[a]=nc; for(int i=0;i<nc;i++) CE[a][i]=cur[i];
    ll bp=-1,bq=1;
    for(int i=0;i<nc;i++){
      ll p=cur[i].hi_n*cur[i].lo_d-cur[i].lo_n*cur[i].hi_d, q=cur[i].hi_d*cur[i].lo_d;
      if(bp<0 || p*bq>bp*q){bp=p;bq=q;}
    }
    Lp[a]=bp; Lq[a]=bq; /* bp=-1 : empty */
  }
}

static void process(int c1, int c2){
  ll ds[16]; int nd=0;
  for(int i=0;i<mD;i++) ds[nd++]=Dp[i];
  if(R>=1) ds[nd++]=8LL*c1;
  if(R>=2) ds[nd++]=8LL*c2;
  HIT(K_PAIRS,c1,c2);
  ll g=0; for(int i=0;i<nd;i++) g=gcdll(g,ds[i]);
  ll tn,td; int mv; int ok=cascade(nd,ds,&tn,&td,&mv);
  ll on,od; int mask=0; int ok2=openmin(nd,ds,&on,&od,&mask);
  if(ok!=ok2 || (ok && tn*od!=on*td)) HIT(K_MISMATCH,c1,c2);
  if(g>1) HIT(K_GCD_GT1,c1,c2); else HIT(K_GCD1,c1,c2);
  if(mv>mxv[MX[M_MOVES]]){ mxv[MX[M_MOVES]]=mv; mkex(c1,c2); strcpy(mex[MX[M_MOVES]],exbuf);}
  if(!ok){ if(getenv("PF")){ mkex(c1,c2); fprintf(stderr,"F %s\n",exbuf);} HIT(K_FAIL,c1,c2); if(g>1) HIT(K_GCD_GT1_FAIL,c1,c2); else HIT(K_GCD1_FAIL,c1,c2); return; }
  if(R!=1 || DETAIL<1) return;
  int c=c1;
  /* landing */
  ll a = 8*tn/td; ll en = 8*tn - a*td; /* eta = en/td */
  int cl[8]; /* landing a counter */
  HIT(K_LA0+(int)a,c1,c2);
  /* opener(s) */
  int mo=0, dpo=0; ll lapmax=-1; ll dpl=0;
  for(int i=0;i<nd;i++){ ll d=ds[i]; ll nn=8*d*tn-td; if(nn%(8*td)==0){ ll lap=nn/(8*td); if(i==nd-1) mo=1; else { dpo=1; if(lap>lapmax){lapmax=lap;dpl=d;} } } }
  if(mo&&!dpo) HIT(K_OP_MULT,c1,c2); else if(!mo&&dpo) HIT(K_OP_DP,c1,c2); else HIT(K_OP_BOTH,c1,c2);
  if(dpo){ if(lapmax==0) HIT(K_LAP0,c1,c2); else if(lapmax==1) HIT(K_LAP1,c1,c2); else HIT(K_LAP2p,c1,c2);
    if(lapmax>mxv[MX[M_LAP]]){ mxv[MX[M_LAP]]=lapmax; mkex(c1,c2); sprintf(mex[MX[M_LAP]],"%s d=%lld",exbuf,dpl);} }
  /* m: 8c*eta integer? */
  ll mnum = 8LL*c*en; ll m=-1;
  if(mnum%td==0){ m=mnum/td; HIT(K_MINT,c1,c2); if(m==1) HIT(K_M1,c1,c2); } else HIT(K_NONINT,c1,c2);
  if(mo){ /* multiple opens: m = 8j+1 */
    ll j=(m-1)/8;
    if(j==0) HIT(K_J0,c1,c2); else if(j==1) HIT(K_J1,c1,c2); else if(j==2) HIT(K_J2,c1,c2); else if(j<8) HIT(K_J3to7,c1,c2); else if(j<16) HIT(K_J8to15,c1,c2); else HIT(K_J16p,c1,c2);
    if(j>mxv[MX[M_J]]){ mxv[MX[M_J]]=j; mkex(c1,c2); sprintf(mex[MX[M_J]],"%s a=%lld m=%lld",exbuf,a,m);} }
  /* residues at landing a */
  int has0=0,has7=0; for(int i=0;i<mD;i++){ int r=(int)((Dp[i]*a)%8); if(r==0) has0=1; if(r==7) has7=1; }
  if(has0) HIT(K_LAND_HAS0,c1,c2); if(has7) HIT(K_LAND_HAS7,c1,c2); if(!has0&&!has7) HIT(K_LAND_RES_OK,c1,c2);
  int A0=-1, A1=-1;
  for(int aa=0;aa<8;aa++){ int h0=0,h7=0; for(int i=0;i<mD;i++){ int r=(int)((Dp[i]*aa)%8); if(r==0)h0=1; if(r==7)h7=1; }
    if(!h0 && A0<0) A0=aa; if(!h0&&!h7&&A1<0) A1=aa; }
  if(A1>=0) HIT(K_A1_EXISTS,c1,c2); else HIT(K_A1_NONE,c1,c2);
  if(A1==a) HIT(K_LAND_EQ_A1,c1,c2); if(A0==a) HIT(K_LAND_EQ_A0,c1,c2);
  if(A1<0 && !(has0||has7)) {/* impossible */}
  if(has0||has7) HIT(K_NEEDS_RES07,c1,c2);
  /* families: s = a + m/(8c), m=1..8c-1, m mod 8 != 0 (multiple clear iff m mod 8 in 1..7), D' clear */
  {
    ll mmin=-1, mmin1=-1; int f1any=0, f1a1=0;
    for(ll mm=1; mm<8LL*c; mm++){
      if(mm%8==0) continue;
      for(int aa=0;aa<8;aa++){
        ll num=8LL*c*aa+mm, den=64LL*c;
        int ok1=1;
        for(int i=0;i<mD;i++){ ll r=(Dp[i]*num)%den; ll mn=r<den-r?r:den-r; if(mn<8LL*c){ok1=0;break;} }
        if(ok1){ if(mmin<0) mmin=mm; if(mm==1){ f1any=1; if(aa==A1) f1a1=1; } }
        if(ok1 && aa==A1 && mmin1<0) mmin1=mm;
      }
      if(mmin>=0) break;
    }
    if(mmin<0) HIT(K_G_ANY_FAIL,c1,c2);
    /* F1: m=1 any a */
    if(f1any) HIT(K_F1_ANY,c1,c2); else HIT(K_F1_ANY_FAIL,c1,c2);
    if(A1>=0){ if(f1a1) HIT(K_F1_A1,c1,c2); else HIT(K_F1_A1_FAIL,c1,c2); }
    /* F_mult: m = 1 mod 8, any a */
    int fm=0; for(ll mm=1; mm<8LL*c && !fm; mm+=8) for(int aa=0;aa<8&&!fm;aa++){
        ll num=8LL*c*aa+mm, den=64LL*c; int ok1=1;
        for(int i=0;i<mD;i++){ ll r=(Dp[i]*num)%den; ll mn=r<den-r?r:den-r; if(mn<8LL*c){ok1=0;break;} }
        if(ok1) fm=1; }
    if(!fm) HIT(K_FM_ANY_FAIL,c1,c2);
    /* F_mult at the landing a only */
    int fl=0; for(ll mm=1; mm<8LL*c && !fl; mm+=8){ ll num=8LL*c*a+mm, den=64LL*c; int ok1=1;
        for(int i=0;i<mD;i++){ ll r=(Dp[i]*num)%den; ll mn=r<den-r?r:den-r; if(mn<8LL*c){ok1=0;break;} }
        if(ok1) fl=1; }
    if(!fl) HIT(K_FMULT_AT_LANDINGA_FAIL,c1,c2);
    if(mmin>=0){ /* store max mmin (absolute) and max mmin/c */
      if(mmin>mxv[MX[M_MMIN]]){ mxv[MX[M_MMIN]]=mmin; mkex(c1,c2); strcpy(mex[MX[M_MMIN]],exbuf);} }
  }

  /* exact unit criterion and landing formula via cells */
  {
    int emask=0; ll bn2=-1, bd2=1; int bfound=0; int ordi=0, succ=-1; int skbig=0;
    for(int aa=0;aa<8;aa++){
      for(int i=0;i<NCE[aa];i++){
        ll xn=CE[aa][i].lo_n, xd=CE[aa][i].lo_d, yn=CE[aa][i].hi_n, yd=CE[aa][i].hi_d;
        ll u=(ll)c*xn, v=xd; ll r=u%v; ll mn=r<v-r?r:v-r; ll wn, wd;
        if(8*mn>=v){ wn=xn; wd=xd; }
        else { ll q=cdiv(8*u-v, 8*v); wn=8*q+1; wd=8LL*c; }
        if(succ<0){ if(wn*yd <= yn*wd) succ=ordi; else if(4LL*c*(yn*xd-xn*yd) >= yd*xd) skbig=1; }
        ordi++;
        if(wn*yd <= yn*wd){ emask|=1<<aa; if(!bfound || wn*bd2 < bn2*wd){ bn2=wn; bd2=wd; bfound=1; } }
      }
    }
    if(DETAIL>=2 && emask!=mask) HIT(K_PX_MISMATCH_UNIT,c1,c2);
    if(succ==0) HIT(K_SKIP0,c1,c2); else if(succ==1) HIT(K_SKIP1,c1,c2); else if(succ==2) HIT(K_SKIP2,c1,c2); else HIT(K_SKIP3p,c1,c2);
    if(skbig) HIT(K_SKIPPED_BIG,c1,c2);
    /* landing s* = 8tn/td versus bn2/bd2 */
    if(!bfound || 8*tn*bd2 != bn2*td) HIT(K_PX_MISMATCH_LAND,c1,c2);
    int apos=-1; for(int aa=0;aa<8;aa++){ for(int i=0;i<NCE[aa];i++){ if(CE[aa][i].hi_n*CE[aa][i].lo_d > CE[aa][i].lo_n*CE[aa][i].hi_d){apos=aa;break;} } if(apos>=0)break; }
    if(apos<0) HIT(K_NOAPOS,c1,c2);
    else { if(a<apos) HIT(K_LAND_LT_APOS,c1,c2); else if(a==apos) HIT(K_LAND_EQ_APOS,c1,c2); else HIT(K_LAND_GT_APOS,c1,c2);
      if(4LL*c*Lp[apos]>=Lq[apos]){ HIT(K_BIGAPOS,c1,c2); if(a!=apos) HIT(K_BIGAPOS_LAND_NEQ_APOS,c1,c2); } }
  }
  /* sufficient window criterion for F1@A1 */
  if(A1>=0){
    int suff=1; for(int i=0;i<mD;i++){ ll rd=(Dp[i]*A1)%8; /* need d/(8c) <= 7-rd  <=> d <= 8c(7-rd) */ if(Dp[i] > 8LL*c*(7-rd)){suff=0;break;} }
    /* actual F1@A1 */
    ll num=8LL*c*A1+1, den=64LL*c; int ok1=1; for(int i=0;i<mD;i++){ ll r=(Dp[i]*num)%den; ll mn=r<den-r?r:den-r; if(mn<8LL*c){ok1=0;break;} }
    if(suff) HIT(K_SUFF_A1,c1,c2);
    if(suff&&!ok1) HIT(K_SUFF_NOT_F1,c1,c2);
    if(ok1&&!suff) HIT(K_F1_NOT_SUFF,c1,c2);
  }
  /* cells: Big(c) = {a : 4 c p >= q} */
  {
    int big=0; int minbig=-1;
    for(int aa=0;aa<8;aa++) if(Lp[aa]>=0 && 4LL*c*Lp[aa]>=Lq[aa]){ big|=1<<aa; if(minbig<0) minbig=aa; }
    if(!big) HIT(K_BIG_EMPTY,c1,c2);
    else { if(big>>a&1) HIT(K_LAND_IN_BIG,c1,c2); else HIT(K_LAND_NOTIN_BIG,c1,c2);
           if(minbig==a) HIT(K_LAND_EQ_MINBIG,c1,c2); else HIT(K_LAND_NEQ_MINBIG,c1,c2); }
    if(DETAIL>=2){
      for(int aa=0;aa<8;aa++){ int b=(big>>aa)&1, l=(mask>>aa)&1;
        if(b&&l) HIT(K_BIGLONE_BB,c1,c2); else if(b&&!l) HITX(K_BIGLONE_BN,c1,c2,"(a in Big, no lonely point in unit a)"); else if(!b&&l) HIT(K_BIGLONE_NB,c1,c2); else HIT(K_BIGLONE_NN,c1,c2); }
      if(!big && mask) HIT(K_BIGEMPTY_LONE,c1,c2);
      /* landing a is the least a with a lonely point (consistency) */
      int ml=-1; for(int aa=0;aa<8;aa++) if(mask>>aa&1){ml=aa;break;}
      if(ml==a) HIT(K_LAND_EQ_MINLONE_A,c1,c2);
    }
  }
}

static void rec(int pos, int start){
  if(pos==mD){
    if((idx_counter++)%W!=WK) return;
    if(R>=1 && DETAIL>=1){
      cells();
      ll bp=-1,bq=1; for(int a=0;a<8;a++) if(Lp[a]>=0 && (bp<0 || Lp[a]*bq>bp*Lq[a])){bp=Lp[a];bq=Lq[a];}
      if(bp==0) { cnt[K[K_DP_ZEROLEN]]++; if(!cex[K[K_DP_ZEROLEN]][0]){ mkex(0,0); strcpy(cex[K[K_DP_ZEROLEN]],exbuf);} }
      if(bp>0 && mD>0){ ll dmax=Dp[mD-1]; ll c0=cdiv(bq,4*bp);
        if(c0>mxv[MX[M_C0]]){ mxv[MX[M_C0]]=c0; mkex(0,0); sprintf(mex[MX[M_C0]],"%s Lmax=%lld/%lld",exbuf,bp,bq);} 
        ll enc = 1000000000000LL - (1000000000000LL*bp*dmax)/bq;
        if(enc>mxv[MX[M_RATIO]]){ mxv[MX[M_RATIO]]=enc; mkex(0,0); sprintf(mex[MX[M_RATIO]],"%s Lmax=%lld/%lld dmax=%lld",exbuf,bp,bq,dmax);} }
    }
    if(R==0) process(0,0);
    else if(R==1) for(int c=1;c<=CM;c++) process(c,0);
    else for(int c1=1;c1<=CM;c1++) for(int c2=c1+1;c2<=CM;c2++) process(c1,c2);
    return;
  }
  for(int i=start;i<nal;i++){ Dp[pos]=allowed[i]; rec(pos+1,i+1); }
}

int main(int argc,char**argv){
  /* args: mD R N CM DETAIL W WK [exactN] */
  mD=atoi(argv[1]); R=atoi(argv[2]); N=atoi(argv[3]); CM=atoi(argv[4]); DETAIL=atoi(argv[5]); W=atoi(argv[6]); WK=atoi(argv[7]);
  int Nlo = argc>8 ? atoi(argv[8]) : 1; /* if >1: restrict to sets containing at least one element >= Nlo is NOT done; kept for completeness */
  (void)Nlo;
  nal=0; for(int d=1;d<=N;d++) if(d%8) allowed[nal++]=d;
  #define REG(e,n) K[e]=reg(n)
  REG(K_PAIRS,"pairs");REG(K_FAIL,"FAIL_no_lonely_instant");REG(K_MISMATCH,"MISMATCH_cascade_vs_openmin");REG(K_GCD_GT1,"pairs_gcd>1");REG(K_GCD_GT1_FAIL,"fail_gcd>1");REG(K_GCD1,"pairs_gcd=1");REG(K_GCD1_FAIL,"fail_gcd=1");
  REG(K_OP_MULT,"opener_multiple_only");REG(K_OP_DP,"opener_Dprime_only");REG(K_OP_BOTH,"opener_both");REG(K_M1,"landing_eta=1/(8c)");REG(K_MINT,"landing_8c*eta_integer");REG(K_NONINT,"landing_8c*eta_not_integer");
  REG(K_LA0,"landing_a=0");REG(K_LA1,"landing_a=1");REG(K_LA2,"landing_a=2");REG(K_LA3,"landing_a=3");REG(K_LA4,"landing_a=4");REG(K_LA5,"landing_a=5");REG(K_LA6,"landing_a=6");REG(K_LA7,"landing_a=7");
  REG(K_A1_EXISTS,"A1_exists(a with all d*a mod 8 in 1..6)");REG(K_A1_NONE,"A1_none");REG(K_LAND_EQ_A1,"landing_a==A1(least)");REG(K_LAND_EQ_A0,"landing_a==A0(least a with no d*a=0 mod 8)");
  REG(K_LAND_RES_OK,"landing_a_residues_all_in_1..6");REG(K_LAND_HAS0,"landing_a_has_residue0");REG(K_LAND_HAS7,"landing_a_has_residue7");
  REG(K_F1_ANY,"F1:exists_a_lonely_at_a+1/(8c)");REG(K_F1_ANY_FAIL,"F1_FAIL:no_a_lonely_at_a+1/(8c)");REG(K_F1_A1,"F1@A1:lonely_at_A1+1/(8c)");REG(K_F1_A1_FAIL,"F1@A1_FAIL(A1 exists)");
  REG(K_FM_ANY_FAIL,"Fmult_FAIL:no_a,j_lonely_at_a+(j+1/8)/c");REG(K_FMULT_AT_LANDINGA_FAIL,"Fmult@landing_a_FAIL");REG(K_G_ANY_FAIL,"G_FAIL:no_a,m_lonely_at_a+m/(8c)");
  REG(K_BIG_EMPTY,"Big(c)_empty");REG(K_LAND_IN_BIG,"landing_a_in_Big");REG(K_LAND_NOTIN_BIG,"landing_a_NOT_in_Big(Big nonempty)");REG(K_LAND_EQ_MINBIG,"landing_a==min_Big");REG(K_LAND_NEQ_MINBIG,"landing_a!=min_Big(Big nonempty)");
  REG(K_BIGLONE_BB,"cell(a,c):Big&lonely_in_unit");REG(K_BIGLONE_BN,"cell(a,c):Big&NO_lonely_in_unit");REG(K_BIGLONE_NB,"cell(a,c):notBig&lonely_in_unit");REG(K_BIGLONE_NN,"cell(a,c):notBig&no_lonely");REG(K_BIGEMPTY_LONE,"pairs:Big_empty_but_lonely_exists");
  REG(K_J0,"mult_opens_j=0");REG(K_J1,"mult_opens_j=1");REG(K_J2,"mult_opens_j=2");REG(K_J3to7,"mult_opens_j=3..7");REG(K_J8to15,"mult_opens_j=8..15");REG(K_J16p,"mult_opens_j>=16");REG(K_LAND_EQ_MINLONE_A,"landing_a==least_a_with_lonely_point");
  REG(K_MULTIPLE_FIRST_GE,"unused");REG(K_LAND_A_IS_FIRSTRES,"unused2");REG(K_LAP0,"Dprime_opener_lap0");REG(K_LAP1,"Dprime_opener_lap1");REG(K_LAP2p,"Dprime_opener_lap>=2");REG(K_NEEDS_RES07,"landing_a_has_residue_0_or_7");REG(K_DEXC,"unused3");
  REG(K_SUFF_A1,"SUFF:A1_exists&c>=d/(8(7-r_d))_all_d");REG(K_SUFF_NOT_F1,"SUFF_true_but_F1@A1_false(expect 0)");REG(K_F1_NOT_SUFF,"F1@A1_true_but_SUFF_false(wrap-around)");
  REG(K_PX_MISMATCH_UNIT,"EXACT_unit_criterion(w_c(x)<=y)_vs_lonely_in_unit_MISMATCH(expect0)");REG(K_PX_MISMATCH_LAND,"EXACT_landing=w_c(x)_of_first_good_cell_MISMATCH(expect0)");
  REG(K_LAND_LT_APOS,"landing_a<a_pos(least a with positive-length D'-cell)");REG(K_LAND_EQ_APOS,"landing_a==a_pos");REG(K_LAND_GT_APOS,"landing_a>a_pos");
  REG(K_BIGAPOS,"c>=1/(4L_apos)(cell of a_pos is Big)");REG(K_BIGAPOS_LAND_NEQ_APOS,"  of which landing_a!=a_pos");REG(K_NOAPOS,"D'_with_no_positive_length_cell(pairs)");REG(K_SKIP0,"landing_cell_is_the_FIRST_D'-cell(in s order)");REG(K_SKIP1,"landing_cell_is_the_2nd_cell(1 skipped)");REG(K_SKIP2,"landing_cell_is_the_3rd(2 skipped)");REG(K_SKIP3p,"landing_cell_is_4th_or_later");REG(K_SKIPPED_BIG,"a_skipped_cell_had_length>=1/(4c)(expect0)");
  REG(K_DP_ZEROLEN,"D'(sets)_whose_longest_cell_has_length_0");
  MX[M_MOVES]=regm("max_cascade_moves"); MX[M_J]=regm("max_j_when_multiple_opens"); MX[M_MMIN]=regm("max_over_pairs_of_least_m_in_G"); MX[M_LAP]=regm("max_lap_of_Dprime_opener"); MX[M_DPLAND]=regm("unused"); MX[M_MMINA1]=regm("unused"); MX[M_C0]=regm("max_over_D'_of_c0=ceil(1/(4*Lmax))"); MX[M_RATIO]=regm("MIN_over_D'_of_Lmax*d_max (encoded 10^12-floor(10^12*value))");
  rec(0,0);
  for(int i=0;i<ncnt;i++) printf("C\t%s\t%lld\t%s\n",cname[i],cnt[i],cex[i]);
  for(int i=0;i<nmx;i++) printf("M\t%s\t%lld\t%s\n",mname[i],mxv[i],mex[i]);
  return 0;
}
'''

SRC = os.path.join(SCR, "om.c")
BIN = os.path.join(SCR, "om")

def build():
    open(SRC, "w").write(C_SRC)
    subprocess.run(["clang", "-O2", "-o", BIN, SRC, "-Wno-unused-value", "-Wno-unused-but-set-variable"], check=True)

NW = 10

def run_block(mD, R, N, CM, DETAIL, label):
    t0 = time.time()
    procs = []
    for w in range(NW):
        procs.append(subprocess.Popen([BIN, str(mD), str(R), str(N), str(CM), str(DETAIL), str(NW), str(w)],
                                      stdout=subprocess.PIPE, text=True))
    agg = {}; mx = {}; order = []
    for p in procs:
        out = p.communicate()[0]
        if p.returncode != 0: raise SystemExit(f'worker failed rc={p.returncode}')
        for line in out.splitlines():
            parts = line.split("\t")
            if parts[0] == "C":
                n, v, ex = parts[1], int(parts[2]), parts[3] if len(parts) > 3 else ""
                if n not in agg: agg[n] = [0, ""]; order.append(n)
                agg[n][0] += v
                if ex and (not agg[n][1] or ex < agg[n][1]): agg[n][1] = ex
            else:
                n, v, ex = parts[1], int(parts[2]), parts[3] if len(parts) > 3 else ""
                if n not in mx or v > mx[n][0] or (v == mx[n][0] and ex and (not mx[n][1] or ex < mx[n][1])): mx[n] = [v, ex]
    print("=" * 100)
    print(f"BLOCK {label}: |D'|={mD}, multiples={R}, D' subset of {{1..{N}}} not div by 8, c in 1..{CM}"
          + (" (c1<c2)" if R == 2 else "") + f", detail={DETAIL}; time {time.time()-t0:.1f}s")
    for n in order:
        if n.startswith("unused"): continue
        v, ex = agg[n]
        if R != 1 and n not in ("pairs", "FAIL_no_lonely_instant", "MISMATCH_cascade_vs_openmin", "pairs_gcd>1", "fail_gcd>1", "pairs_gcd=1", "fail_gcd=1"): continue
        print(f"  {n:60s} {v:>12d}   {('first: ' + ex) if ex and v else ''}")
    if R == 1 and DETAIL >= 1:
        for n, (v, ex) in mx.items():
            if n.startswith("unused"): continue
            print(f"  MAX {n:56s} {v:>12d}   {ex}")
    elif "max_cascade_moves" in mx:
        print(f"  MAX max_cascade_moves {mx['max_cascade_moves'][0]}  {mx['max_cascade_moves'][1]}")
    sys.stdout.flush()
    return agg, mx


def exact_py_checks():
    """Small pure-Python Fraction cross-check of the C kernel (independent code path) on a slice."""
    def dist(x): return abs(x - round(x))
    def lonely_min(ds):
        # candidate left ends, Fractions
        best = None
        for d in ds:
            for k in range(d):
                t = Fraction(8 * k + 1, 8 * d)
                if all(dist(e * t) >= Fraction(1, 8) for e in ds):
                    if best is None or t < best: best = t
        return best
    def cascade(ds):
        t = Fraction(1, 8 * min(ds))
        while True:
            way = [d for d in ds if dist(d * t) < Fraction(1, 8)]
            if not way: return t
            nxt = max((Fraction(math_ceil(d * t - Fraction(1, 8)), 1) + Fraction(1, 8)) / d for d in way)
            t = nxt
            if t >= 1: return None
    import math
    def math_ceil(x): return math.ceil(x)
    bad = 0; n = 0
    allowed = [d for d in range(1, 15) if d % 8]
    for D in itertools.combinations(allowed, 4):
        for c in range(1, 25):
            ds = list(D) + [8 * c]
            a = cascade(ds); b = lonely_min(ds); n += 1
            if a != b: bad += 1
    print(f"PYTHON Fraction cross-check (independent of C): D' of size 4 in {{1..14}}\\8Z, c<=24: {n} pairs, cascade==least-opening mismatches: {bad}")
    # signed / zero / duplicate reductions (exact, small)
    def lonely_exists_signed(ds):
        # general integers incl. negative & repeats: distInt(d t) = distInt(|d| t); zero never clear
        if any(d == 0 for d in ds): return False
        return lonely_min(sorted(set(abs(d) for d in ds))) is not None
    cnt0 = 0
    for D in itertools.combinations(allowed, 3):
        for c in range(0, 6):
            ds = list(D) + [8 * c]
            if lonely_exists_signed(ds) is False and c != 0: cnt0 += 1
    print(f"PYTHON: c=0 (speed 0 runner): lonely exists? {lonely_exists_signed([1,2,3,0])}  (distInt(0*t)=0<1/8 for all t)")
    print(f"PYTHON: c>=1 pairs (D' size 3, c 1..5) without lonely instant: {cnt0}")
    # sign invariance and repeats
    ok = True
    for D in itertools.combinations(allowed, 3):
        for c in range(1, 5):
            base = sorted(list(D) + [8 * c])
            for sg in itertools.product([1, -1], repeat=4):
                dd = [s * x for s, x in zip(sg, base)] + [base[0], base[0]]  # signs + repeated elements
                if (lonely_exists_signed(dd) is True) != (lonely_min(base) is not None): ok = False
    print(f"PYTHON: sign flips and repeated elements leave the existence verdict unchanged on D' size 3, c<=4: {ok}")
    # gcd scaling identity: D=g*E lonely iff E lonely  (t -> g t); checked on slice
    ok = True; nn = 0
    for E in itertools.combinations(range(1, 13), 3):
        for g in (2, 3, 5, 6):
            nn += 1
            if (lonely_min(sorted(g * e for e in E)) is not None) != (lonely_min(list(E)) is not None): ok = False
    print(f"PYTHON: scaling D=gE (g in 2,3,5,6) preserves existence verdict, {nn} slices: {ok}")

def fail_analysis():
    """Collect every failing (D', c) of the |D'|=7 + one multiple population and test which extra hypotheses would remove them."""
    import re, collections
    from math import gcd
    from functools import reduce
    for (N, CM) in ((14, 48), (22, 48), (30, 40)):
        fails = []
        procs = [subprocess.Popen([BIN, "7", "1", str(N), str(CM), "0", str(NW), str(w)], stdout=subprocess.DEVNULL,
                                  stderr=subprocess.PIPE, text=True, env=dict(os.environ, PF="1")) for w in range(NW)]
        for p in procs:
            for line in p.communicate()[1].splitlines():
                m = re.match(r"F D'=([\d,]+), c=(\d+)", line)
                if m: fails.append((tuple(int(x) for x in m.group(1).strip(",").split(",")), int(m.group(2))))
        fails.sort()
        sets = sorted(set(D for D, c in fails))
        print("=" * 100)
        print(f"FAIL ANALYSIS |D'|=7 + one multiple 8c, N={N}, c<=CM={CM}: failing pairs {len(fails)}, distinct failing D' {len(sets)}")
        for D in sets:
            cs = [c for DD, c in fails if DD == D]
            odd = sorted(set(d % 8 for d in D if d % 2))
            print(f"   D'={D}  failing c: {'ALL 1..%d' % CM if len(cs) == CM else cs}  odd residues present {odd}  gcd(D')={reduce(gcd, D)}")
        print("   failing pairs whose D' misses an odd residue class mod 8: %d" % sum(1 for D, c in fails if len(set(d % 8 for d in D if d % 2)) < 4))
        print("   failing pairs with gcd(D' u 8c) > 1: %d" % sum(1 for D, c in fails if reduce(gcd, list(D) + [8 * c]) > 1))


def example_tables():
    """Exact Fraction tables for chosen D' (independent of the C kernel): longest D'-compatible cell per unit a
    (length L_a in s = 8t units), Big(c) = {a : L_a >= 1/(4c)}, and the cascade landing s* = a + eta."""
    import math
    F = Fraction
    def dist(x): return abs(x - round(x))
    def cells_for(Dp):
        out = []
        for a in range(8):
            cur = [(F(a), F(a + 1))]
            for d in Dp:
                nw = []
                for (lo, hi) in cur:
                    k0 = max(0, math.floor(lo * d / 8) - 1); k1 = math.ceil(hi * d / 8) + 1
                    for k in range(k0, k1 + 1):
                        l2 = max(lo, F(8 * k + 1, d)); h2 = min(hi, F(8 * k + 7, d))
                        if l2 <= h2: nw.append((l2, h2))
                cur = nw
            out.append(cur)
        return out
    def landing(ds):
        t = F(1, 8 * min(ds))
        while True:
            way = [d for d in ds if dist(d * t) < F(1, 8)]
            if not way: return 8 * t if t < 1 else None
            t = max((math.ceil(d * t - F(1, 8)) + F(1, 8)) / d for d in way)
            if t >= 1: return None
    print("=" * 100)
    print("EXAMPLE TABLES (Fractions).  L_a = longest cell of the D'-compatible set inside [a,a+1] (s units); '-' = empty.")
    for Dp in [(1,2,3,4,5,6),(1,2,3,4,5,7),(1,5,6,7,11,13),(1,4,5,6,7,11),(1,2,3,4,6,9),(3,6,9,12,15,21),(1,2,3,4,5,6,7)]:
        cl = cells_for(Dp)
        Ls = [max((h - l for l, h in cl[a]), default=None) for a in range(8)]
        print(f"D'={Dp}")
        print("   L_a (a=0..7): " + "  ".join(("-" if L is None else str(L)) for L in Ls))
        for c in (1, 2, 3, 5, 8, 13, 21, 50, 100):
            ds = list(Dp) + [8 * c]
            big = [a for a in range(8) if Ls[a] is not None and Ls[a] >= F(1, 4 * c)]
            ld = landing(ds)
            if ld is None: print(f"   c={c:4d}: NO lonely instant; Big={big}")
            else:
                a = math.floor(ld); eta = ld - a
                m = 8 * c * eta
                print(f"   c={c:4d}: landing s*={ld} = {a} + {eta};  8c*eta={m}  Big(c)={big}  landing a in Big: {a in big}")


if __name__ == "__main__":
    t_start = time.time()
    build()
    print(__doc__)
    exact_py_checks()
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("all", "T"): example_tables()
    if which in ("all", "F"): fail_analysis()
    # Block A: exact re-run of the known population
    if which in ("all", "A"):
        for N in (14, 18, 22):
            run_block(6, 1, N, 48, 2, f"A (known population part, N={N}: 1716, 8008, 38760 sets x 48)")
    if which in ("all", "B"):
        for k in range(1, 6):
            run_block(k, 1, 22, 48, 2, f"B1 |D'|={k}, N=22, c<=48")
        run_block(6, 1, 30, 100, 2, "B2 |D'|=6, N=30, c<=100")
        run_block(6, 1, 14, 600, 2, "B3 |D'|=6, N=14, c<=600 (large c, small N)")
        run_block(6, 1, 22, 150, 2, "B4 |D'|=6, N=22, c<=150")
    if which in ("all", "C"):
        run_block(6, 1, 40, 60, 1, "C1 |D'|=6, N=40, c<=60")
        run_block(6, 1, 50, 30, 0, "C2 |D'|=6, N=50, c<=30 (cascade+open-min only)")
        run_block(6, 1, 30, 400, 0, "C3 |D'|=6, N=30, c<=400 (cascade+open-min only)")
    if which in ("all", "D"):
        run_block(8, 0, 14, 0, 0, "D0 |D'|=8, NO multiple (8 disparities, threshold 1/8), N=14")
        run_block(6, 2, 14, 24, 0, "D00 |D'|=6 + two multiples (8 disparities), N=14, c<=24")
        run_block(7, 1, 14, 48, 2, "D1 |D'|=7 (8 disparities, threshold 1/8), N=14, c<=48")
        run_block(7, 1, 14, 48, 1, "D1b same as D1 with cell statistics (counts D' sets whose longest cell has length 0)")
        run_block(7, 1, 18, 48, 2, "D2 |D'|=7 (8 disparities, threshold 1/8), N=18, c<=48")
        run_block(7, 1, 22, 48, 2, "D3 |D'|=7 (8 disparities, threshold 1/8), N=22, c<=48")
        run_block(7, 1, 30, 40, 0, "D4 |D'|=7 (8 disparities, threshold 1/8), N=30, c<=40")
        run_block(7, 0, 30, 0, 0, "D5 |D'|=7, NO multiple of 8, N=30")
        run_block(7, 0, 50, 0, 0, "D6 |D'|=7, NO multiple of 8, N=50")
        run_block(8, 1, 22, 24, 0, "D7 |D'|=8 + one multiple (9 disparities, threshold 1/8), N=22, c<=24")
    if which in ("all", "E"):
        for k in range(0, 6):
            run_block(k, 2, 22, 48, 0, f"E1 |D'|={k} + two multiples 8c1,8c2 (c1<c2), N=22, c<=48")
        run_block(5, 2, 30, 40, 0, "E2 |D'|=5 + two multiples, N=30, c<=40")
        run_block(4, 2, 30, 100, 0, "E3 |D'|=4 + two multiples, N=30, c<=100")
    print("TOTAL time %.1fs" % (time.time() - t_start))
