#!/usr/bin/env python3
"""The displaced landing of the cascade chain: exact-arithmetic data [OBS] for Fresh/DisplacedLanding.lean (task BD).

Rules: 1, 5, 6, 7, 13, 15, 16, 18, 21.  Exact only (integers, __int128 and Fractions); no floating point; every cascade loop has a move limit
(LIMIT = 2000 in the C kernel, 100000 in the Fraction reference); no `timeout` command is used.  No pre-registration, no imports of other
frameworks' obligations.  Every count below is [OBS] (a counting tool, never an argument); the Lean statements are in
Fresh/DisplacedLanding.lean and the data only locates and tests them.

Objects.  A set is the 7 disparities of the subject, integers y_0 < ... < y_6 (scale covariant: disparities y_j/Q), m = y_0 = d_min,
rho_j = y_j/m, gate coordinate R = 8 m t.  idx_j = round(rho_j) (tie up, as Lean's `round`), e_j = rho_j - idx_j, ridx_j = (idx_j - 1) mod 8 + 1,
quo_j = (idx_j - 1) div 8.  The cascade from R = 1: reading j is blocked at R iff |rho_j R - 8 z| < 1, z = round(rho_j R / 8); the move goes to
the largest opening (8 z + 1)/rho_j.  Chain R_0 = 1 < R_1 < ... < R_N = R*.  For a step n: setter s_n, lap z_n.

What is tested (each section of the output names the Lean statement it belongs to).
 (C)  chain: R_{n+1} rho_{s_n} = 8 z_n + 1 (landing_step / setter_opening), (R_{n+1}-R_n) rho = 1 - delta (consecutive_difference),
      setter blocked at R_n, R_n < R_{n+1} (final_landing).
 (D)  DISPLACED landing: R* not an integer; a = floor(R*); last mover j, lap z, Ngrid = 8z+1 - a idx_j:
      identity (R*-a) rho_j = Ngrid - a e_j (displaced_identity), a e < Ngrid < idx + (a+1) e (gridPart_bounds), Ngrid = 1 - a idx (mod 8)
      (gridPart_emod), Ngrid = 0 / 1 conditions (gridPart_zero, gridPart_one), slow last mover rho <= 8: lap = floor((a rho - 1)/8) + 1
      (lap_first_opening) and a = 1: Ngrid = (1 - idx) mod 8 (gridPart_one_slow), a = 1 general: Ngrid = (1-idx) mod 8 + 8 w, w >= 0
      (gridPart_one_laps), the last mover's own state at a (self_clear_at_int_iff), the quotient shift (gridPart_quo_shift,
      reduced_reading_at_landing).  The QR statistic (nearest odd integer, no lonely odd integer) is reproduced as a cross-check.
 (F)  FAMILY: a residue-0 reading d0 (ridx = 8): landing = R1 = 1 + (1 - e0)/rho0  iff  lonely at R1 (landing_R1_iff_lonely), tested over
      EVERY ridx-8 reading of every set (the only-blocker hypothesis is not used); when d0 is the only blocker at R = 1 the first move is R1
      (first_move_residue_zero); family_landing_iff (the Win formula with x_d) and family_landing_classes (class inequalities, window);
      the second-move classes (second_move_example).
Populations (all full; no sampling): A(N), N = 16, 20, 24 (every 7-subset of {1..N} with gcd 1); Q = 3 (every 7-subset of {3,..,36} not all
multiples of 3); the families {1..6, Y} (Y = 7..800) and {1,2,3,4,5,7,8k} (exact Fractions).
Usage: python3 displaced_landing_v1.py > displaced_landing_v1.out        (about ten seconds; needs cc; no background process remains)
"""
import os, sys, subprocess, tempfile, shutil, time
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from collections import Counter

C_SRC = r'''/* Exact integer kernel for displaced_landing_v1.py (task BD).  No floating point. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long ll; typedef __int128 LL;
#define LIMIT 2000
#define NH 200
static ll gcdl(ll a, ll b){ if(a<0)a=-a; if(b<0)b=-b; while(b){ll t=a%b;a=b;b=t;} return a; }
static ll fl(LL x, LL d){ LL q=x/d; if((x%d!=0)&&((x<0)!=(d<0))) q--; return (ll)q; }
static ll mod8(ll x){ ll r=x%8; if(r<0)r+=8; return r; }
static ll modp(LL x, LL d){ LL r=x%d; if(r<0)r+=d; return (ll)r; }
/* reading y blocked at R = num/den (base m): |y num - 8 z m den| < m den, z = round(y num / (8 m den)) */
static int blocked(ll y, ll m, ll num, ll den){
  LL xn=(LL)y*num, xd=(LL)m*den; LL z=(xn+4*xd)/(8*xd); LL dev=xn-8*z*xd; if(dev<0)dev=-dev; return dev<xd; }
static void gi(ll y, ll m, ll*idx, ll*er){ ll q=y/m, r=y%m; if(2*r<m){*idx=q;*er=r;} else {*idx=q+1;*er=r-m;} }

#define CNTS(X) \
 X(total) X(nofix) X(land1) X(landInt) X(landNonInt) X(dispNoInt) X(nonIntButInt) \
 X(chainIdViol) X(chainDiffViol) X(chainBlockedViol) X(chainMonoViol) X(nmoves) \
 X(idViol) X(boundViol) X(modViol) X(quoViol) X(redViol) \
 X(Nneg) X(Nzero) X(None) X(N2to7) X(Nge8) \
 X(N0) X(N0viol) X(N1) X(N1viol) X(N1oddviol) \
 X(slow) X(slowLapViol) X(slowOne) X(slowOneViol) X(slowZeroViol) \
 X(fast) X(fastLapFirst) X(fastLapNotFirst) X(aOne) X(oneLapsViol) X(oneBoundViol) \
 X(selfWin) X(selfWinViol) X(selfNoWin) X(selfBlocked) X(selfClear) \
 X(lastBlockedAt1) X(lastNotBlockedAt1) X(lastTies) \
 X(QRdisp) X(QRidViol) \
 X(famPairs) X(famLand) X(famIffViol) X(famNonUniqueLand) X(famNonUniqueMoveNotR1) \
 X(uniq) X(uniqFirstMoveViol) X(uniqLand) X(uniqSecond) X(uniqFormViol) X(uniqWinOK) X(uniqWinBad) \
 X(uniqClassViol) X(uniqBadClassWrong) X(uniqMultiBlocked) \
 X(selfN1) X(selfN0) X(selfN2) X(selfOther) X(selfBlockedN1) X(selfBlockedN0) X(selfBlockedN2) X(selfBlockedOther) \
 X(lapFirstAll) X(lapFirstAllViol) X(prevWinViol) X(prevBelowA) X(prevAtOrAboveA) X(stepWinViol) X(stepFirstViol) X(evenIntNoOdd) X(genPairs) X(genLand) X(genIffViol)
#define X(n) C_##n,
enum { CNTS(X) C_NC };
#undef X
#define X(n) #n,
static const char* CN[] = { CNTS(X) };
#undef X
static ll C[C_NC];
static ll maxMoves=0;
static ll hGenPairs[9], hGenLand[9], hGenViolC[9], hStepN[NH], hNoddEven[NH], hN[NH], hNodd[NH], hW[NH], hRidxLast[9], hA[64], hSecond[64], hNzeroRidx[9], hMoves[64], hNres[8];
#define NWIT 12
static ll wit[NWIT][7]; static int witset[NWIT];
static void setwit(int k, const ll*S){ if(!witset[k]){ witset[k]=1; memcpy(wit[k],S,7*sizeof(ll)); } }
static ll lo,hi,Qm; static int mode; static int part=0,nparts=1; static ll cnt3=0; static ll S[7];

static int lonelyAt(const ll*y, ll m, ll num, ll den){ for(int j=0;j<7;j++) if(blocked(y[j],m,num,den)) return 0; return 1; }
static int lonelyInt(const ll*y,ll m,ll a){ for(int j=0;j<7;j++){ ll r=(ll)(((LL)y[j]*a)%(8*(LL)m)); if(r<m||r>7*m) return 0; } return 1; }

static ll mvj[LIMIT+2], mvz[LIMIT+2], mvn[LIMIT+2], mvd[LIMIT+2], mvt[LIMIT+2];
static void visit(void){
  ll m=S[0]; C[C_total]++;
  ll num=1,den=1; int nmv=0; mvn[0]=1; mvd[0]=1;
  for(;;){
    int best=-1; ll bz=0,bn=0,bd=1; int ties=0;
    for(int j=0;j<7;j++){
      LL xn=(LL)S[j]*num, xd=(LL)m*den; ll z=(ll)((xn+4*xd)/(8*xd)); LL dev=xn-(LL)8*z*xd; if(dev<0)dev=-dev;
      if(dev<xd){ ll nn=(8*z+1)*m, nd=S[j];
        if(best<0 || (LL)nn*bd>(LL)bn*nd){best=j;bz=z;bn=nn;bd=nd;ties=1;}
        else if((LL)nn*bd==(LL)bn*nd) ties++; } }
    if(best<0) break;
    if(nmv>=LIMIT){ C[C_nofix]++; return; }
    ll g=gcdl(bn,bd); num=bn/g; den=bd/g;
    mvj[nmv]=best; mvz[nmv]=bz; mvt[nmv]=ties; nmv++; mvn[nmv]=num; mvd[nmv]=den;
  }
  if(nmv>maxMoves){ maxMoves=nmv; setwit(10,S); }
  C[C_nmoves]+=nmv; if(nmv<64) hMoves[nmv]++;
  /* (C) chain identities */
  for(int n=0;n<nmv;n++){
    int j=(int)mvj[n]; ll z=mvz[n]; ll n0=mvn[n],d0=mvd[n],n1=mvn[n+1],d1=mvd[n+1];
    if((LL)n1*S[j] != (LL)(8*z+1)*m*d1) C[C_chainIdViol]++;
    LL lhs=((LL)n1*d0-(LL)n0*d1)*S[j];
    LL rhs=(LL)m*d0*d1-((LL)S[j]*n0*d1-(LL)8*z*m*d0*d1);
    if(lhs!=rhs) C[C_chainDiffViol]++;
    if(!blocked(S[j],m,n0,d0)) C[C_chainBlockedViol]++;
    if(!((LL)n1*d0>(LL)n0*d1)) C[C_chainMonoViol]++;
  }
  ll idxv[7],erv[7],ridx[7],quo[7],yt[7];
  for(int j=0;j<7;j++){ gi(S[j],m,&idxv[j],&erv[j]); ridx[j]=(idxv[j]-1)%8+1; quo[j]=(idxv[j]-1)/8; yt[j]=S[j]-8*quo[j]*m; }
  for(int n=0;n<nmv;n++){   /* every step, a = 1: the window (rho (R_n - 1) + e, +2) */
    int j=(int)mvj[n]; ll z=mvz[n]; ll N1=8*z+1-idxv[j]; ll pn=mvn[n], pd=mvd[n];
    LL u=(LL)pn-(LL)pd; LL base=(LL)S[j]*u+(LL)erv[j]*pd; LL Nm=(LL)N1*m*pd;
    if(!(base<Nm && Nm<base+(LL)2*m*pd)) C[C_stepWinViol]++;
    if(n==0){ if(!(N1>=0&&N1<=2) || (N1==0&&!(erv[j]<0)) || (N1==2&&!(erv[j]>0))) C[C_stepFirstViol]++; }
    if(N1>=-90&&N1<90) hStepN[N1+90]++;
  }
  int landed1=(num==1&&den==1), landedInt=(den==1);
  if(landed1) C[C_land1]++; else if(landedInt) C[C_landInt]++; else C[C_landNonInt]++;
  ll P=8*m; ll fi=0, fo=0;
  for(ll a=1;a<=P;a++){ if(lonelyInt(S,m,a)){ if(!fi)fi=a; if((a&1)&&!fo)fo=a; if(fi&&fo)break; } }
  if(!landedInt){ if(!fi) C[C_dispNoInt]++; else { C[C_nonIntButInt]++; setwit(3,S); } }
  if(landedInt && !landed1 && !fo){
    C[C_evenIntNoOdd]++;
    ll a=num-1; int j=(int)mvj[nmv-1]; ll z=mvz[nmv-1]; ll N=8*z+1-a*idxv[j];
    if(N>=-90&&N<90) hNoddEven[N+90]++;
  }
  /* ---------------- (D) the displaced landing ---------------- */
  if(!landedInt){
    ll a=num/den;
    int j=(int)mvj[nmv-1]; ll z=mvz[nmv-1]; ll N=8*z+1-a*idxv[j];
    if(mvt[nmv-1]>1) C[C_lastTies]++;
    if(a<64) hA[a]++;
    hRidxLast[ridx[j]]++;
    { ll pn=mvn[nmv-1], pd=mvd[nmv-1];   /* previous landing R0 = pn/pd, u = R0 - a */
      LL u = (LL)pn - (LL)a*pd;           /* u*pd */
      LL base = (LL)S[j]*u + (LL)a*erv[j]*pd;      /* (rho u + a e) * m * pd */
      LL Nm = (LL)N*m*pd;
      if(!(base < Nm && Nm < base + (LL)2*m*pd)) C[C_prevWinViol]++;
      if(u<0) C[C_prevBelowA]++; else C[C_prevAtOrAboveA]++; }
    if((LL)(num-a*den)*S[j] != (LL)(N*m-a*erv[j])*den) C[C_idViol]++;
    if(!((LL)a*erv[j] < (LL)N*m && (LL)N*m < (LL)idxv[j]*m+(LL)(a+1)*erv[j])) C[C_boundViol]++;
    if(mod8(N-(1-a*idxv[j]))!=0) C[C_modViol]++;
    { ll Nred=8*(z-a*quo[j])+1-a*ridx[j]; if(Nred!=N) C[C_quoViol]++; }
    { LL l=(LL)num*yt[j]; LL r=(LL)(8*(z-a*quo[j])+1)*m*den-(LL)8*quo[j]*m*(num-a*den); if(l!=r) C[C_redViol]++; }
    if(N<0){ C[C_Nneg]++; setwit(1,S);} else if(N==0){ C[C_Nzero]++; setwit(0,S); hNzeroRidx[ridx[j]]++; }
    else if(N==1){ C[C_None]++; setwit(7,S);} else if(N<8) C[C_N2to7]++; else C[C_Nge8]++;
    if(N>=-90&&N<90) hN[N+90]++;
    hNres[mod8(N)]++;
    /* N = 0 */
    if(N==0){ C[C_N0]++; if(!( mod8(a*idxv[j])==1 && erv[j]<0 )) C[C_N0viol]++; }
    if(N==1){ C[C_N1]++; if(mod8(a*idxv[j])!=0) C[C_N1viol]++; if((a&1) && mod8(idxv[j])!=0) C[C_N1oddviol]++; }
    /* slow / fast last mover */
    ll lapFirst = fl((LL)a*S[j]-m,(LL)8*m)+1;
    if(S[j]<=8*m){
      C[C_slow]++; if(z!=lapFirst) C[C_slowLapViol]++;
      if(a==1){ C[C_slowOne]++; if(N!=mod8(1-idxv[j]) || (mod8(idxv[j])==1 && !(erv[j]<0))) C[C_slowOneViol]++; }
    } else {
      C[C_fast]++; if(z==lapFirst) C[C_fastLapFirst]++; else { C[C_fastLapNotFirst]++; setwit(5,S); }
    }
    if(z==lapFirst) C[C_lapFirstAll]++; else C[C_lapFirstAllViol]++;
    if(a==1){ C[C_aOne]++;
      ll c=mod8(1-idxv[j]); ll w=(N-c)/8;
      if(N<c || (N-c)%8!=0) C[C_oneLapsViol]++; else { if(w>=0&&w<NH) hW[w]++; if(w>0) setwit(4,S); }
      if(!((LL)N*m < (LL)idxv[j]*m+(LL)2*erv[j])) C[C_oneBoundViol]++; }
    /* the last mover's own state at a */
    { int clear = !blocked(S[j],m,a,1); int win = (LL)(erv[j]<0?-erv[j]:erv[j])*a <= m;
      ll r8=mod8(N); int pred;
      { int c1 = (r8==1) ? ((LL)(erv[j]<0?-erv[j]:erv[j])*a >= m) : 1; int c0 = (r8==0) ? (erv[j]>=0) : 1; int c2 = (r8==2) ? (erv[j]<=0) : 1; pred = c1&&c0&&c2; }
      if(win){ C[C_selfWin]++; if(pred!=clear) C[C_selfWinViol]++; } else { C[C_selfNoWin]++; if(pred!=clear) setwit(11,S); }
      if(clear) C[C_selfClear]++; else C[C_selfBlocked]++;
      if(r8==1){ C[C_selfN1]++; if(!clear) C[C_selfBlockedN1]++; }
      else if(r8==0){ C[C_selfN0]++; if(!clear) C[C_selfBlockedN0]++; }
      else if(r8==2){ C[C_selfN2]++; if(!clear) C[C_selfBlockedN2]++; }
      else { C[C_selfOther]++; if(!clear) C[C_selfBlockedOther]++; } }
    if(blocked(S[j],m,1,1)) C[C_lastBlockedAt1]++; else { C[C_lastNotBlockedAt1]++; setwit(6,S); }
    /* QR cross-check: no lonely odd integer, nearest odd integer to R* */
    if(!fo){
      C[C_QRdisp]++;
      ll ao = (a&1)? a : a+1;
      ll Nodd=8*z+1-ao*idxv[j];
      if((LL)(num-ao*den)*S[j] != (LL)(Nodd*m-ao*erv[j])*den) C[C_QRidViol]++;
      if(Nodd>=-90&&Nodd<90) hNodd[Nodd+90]++;
    }
  }
  /* ---------------- (F) the family of a residue-0 reading ---------------- */
  int bl[7]; int nb=0, firstbl=-1;
  for(int j=0;j<7;j++){ bl[j]=blocked(S[j],m,1,1); if(bl[j]){ nb++; if(firstbl<0)firstbl=j; } }
  for(int j=0;j<7;j++){   /* any reading blocked at R = 1: opening (8 z1 + 1) m / y_j */
    if(!bl[j]) continue;
    ll z1=(S[j]+4*m)/(8*m); ll n1=(8*z1+1)*m, d1=S[j]; ll g=gcdl(n1,d1); n1/=g; d1/=g;
    int lon=lonelyAt(S,m,n1,d1); int isl=(num==n1&&den==d1);
    C[C_genPairs]++; hGenPairs[ridx[j]]++; if(isl){ C[C_genLand]++; hGenLand[ridx[j]]++; }
    if(lon!=isl){ C[C_genIffViol]++; hGenViolC[ridx[j]]++; }
  }
  for(int d0=0; d0<7; d0++){
    if(ridx[d0]!=8) continue;
    ll n1=S[d0]+m-erv[d0], d1=S[d0]; ll g=gcdl(n1,d1); n1/=g; d1/=g;       /* R1 = (y0 + m - er0)/y0 */
    int lon=lonelyAt(S,m,n1,d1); int isl=(num==n1&&den==d1);
    C[C_famPairs]++; if(isl) C[C_famLand]++;
    if(lon!=isl) C[C_famIffViol]++;
    if(nb>=2 && isl){ C[C_famNonUniqueLand]++; setwit(9,S); }
    if(nb>=2 && isl && !(nmv>=1 && mvn[1]==n1 && mvd[1]==d1)) C[C_famNonUniqueMoveNotR1]++;
    if(nb==1 && firstbl==d0){
      C[C_uniq]++;
      if(!(nmv>=1 && mvn[1]==n1 && mvd[1]==d1)) C[C_uniqFirstMoveViol]++;
      if(isl) C[C_uniqLand]++; else C[C_uniqSecond]++;
      /* family_landing_iff: reading of d at R1 is ridx + x_d, formula P/(m d1) */
      int winOK=1, allClassOK=1, allFormulaClear=1, nbl1=0, firstBad=-1;
      for(int j=0;j<7;j++){ if(j==d0) continue;
        ll fnum = modp((LL)quo[j]*n1, d1);
        LL Pq = (LL)yt[j]*n1 + (LL)8*m*fnum;                    /* P / (m d1) = dRed/m * R1 + 8 fract(quo R1) */
        LL md1=(LL)m*d1;
        ll pm = modp(Pq, 8*md1); int formClear = (pm>=md1 && pm<=7*md1);
        int actClear = !blocked(S[j],m,n1,d1);
        if(formClear!=actClear) C[C_uniqFormViol]++;
        if(!actClear){ nbl1++; if(firstBad<0) firstBad=j; allFormulaClear=0; }
        LL xnum = Pq - (LL)ridx[j]*md1;                          /* x_d = xnum/(m d1) */
        LL ax = xnum<0?-xnum:xnum;
        if(ax>md1) winOK=0;
        int c8 = (ridx[j]==8) ? (ax>=md1) : 1; int c1 = (ridx[j]==1) ? (xnum>=0) : 1; int c7 = (ridx[j]==7) ? (xnum<=0) : 1;
        int cls = c8&&c1&&c7;
        if(ax<=md1 && cls!=formClear) C[C_uniqClassViol]++;
        if(!cls) allClassOK=0;
      }
      if(winOK) C[C_uniqWinOK]++; else { C[C_uniqWinBad]++; if(allClassOK && !isl) { C[C_uniqBadClassWrong]++; setwit(8,S);} }
      if(!isl){
        if(nbl1>=2) C[C_uniqMultiBlocked]++;
        int k=firstBad;
        if(k>=0){ int key=(int)(ridx[k]*4 + (quo[k]>0?2:0) + (erv[k]<0?1:0)); if(key<64) hSecond[key]++; if(ridx[k]==7) setwit(2,S); }
      }
    }
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
static void pa(const char*name,ll*arr,int n,int off){ printf("H %s",name); for(int i=0;i<n;i++) if(arr[i]) printf(" %d:%lld",i-off,arr[i]); printf("\n"); }
int main(int argc,char**argv){
  mode = argv[1][0]=='A'?0:1;
  if(mode==0){ lo=1; hi=atoll(argv[2]); Qm=1; } else { Qm=atoll(argv[2]); lo=Qm; hi=12*Qm; }
  part=atoi(argv[3]); nparts=atoi(argv[4]);
  rec(0,lo);
  for(int i=0;i<C_NC;i++) printf("C %s %lld\n",CN[i],C[i]);
  printf("C maxMoves %lld\n",maxMoves);
  pa("hGenPairs",hGenPairs,9,0); pa("hGenLand",hGenLand,9,0); pa("hGenViolC",hGenViolC,9,0); pa("hStepN",hStepN,NH,90); pa("hNoddEven",hNoddEven,NH,90); pa("hN",hN,NH,90); pa("hNodd",hNodd,NH,90); pa("hW",hW,NH,0); pa("hRidxLast",hRidxLast,9,0); pa("hA",hA,64,0);
  pa("hSecond",hSecond,64,0); pa("hNzeroRidx",hNzeroRidx,9,0); pa("hMoves",hMoves,64,0); pa("hNres",hNres,8,0);
  for(int k=0;k<NWIT;k++) if(witset[k]){ printf("W %d",k); for(int j=0;j<7;j++) printf(" %lld",wit[k][j]); printf("\n"); }
  return 0; }
'''

EXE = None
WORK = None
HERE = os.path.dirname(os.path.abspath(__file__))

def build():
    global EXE, WORK
    WORK = tempfile.mkdtemp(prefix='dl_kernel_')
    src = os.path.join(WORK, 'dl.c')
    open(src, 'w').write(C_SRC)
    EXE = os.path.join(WORK, 'dl')
    subprocess.check_call(['cc', '-O2', '-o', EXE, src])

def run_pop(kind, par, nparts):
    procs = [subprocess.Popen([EXE, kind, str(par), str(p), str(nparts)], stdout=subprocess.PIPE, text=True) for p in range(nparts)]
    outs = [pr.communicate()[0] for pr in procs]
    for pr in procs: assert pr.returncode == 0
    M = {'C': Counter(), 'H': {}, 'W': {}}
    for out in outs:
        for line in out.strip().split('\n'):
            tok = line.split()
            if tok[0] == 'C':
                if tok[1] == 'maxMoves': M['C']['maxMoves'] = max(M['C']['maxMoves'], int(tok[2]))
                else: M['C'][tok[1]] += int(tok[2])
            elif tok[0] == 'H':
                h = M['H'].setdefault(tok[1], Counter())
                for kv in tok[2:]:
                    k, v = kv.split(':'); h[int(k)] += int(v)
            elif tok[0] == 'W':
                k = int(tok[1])
                if k not in M['W']: M['W'][k] = tuple(int(x) for x in tok[2:])
    return M

def pct(a, b):
    return '%d/%d' % (a, b) if b else '%d/0' % a

WITNAMES = {0: 'Ngrid = 0 (pure deviation displacement)', 1: 'Ngrid < 0', 2: 'second move, blocker of residue 7',
            3: 'non-integer landing although some integer instant is lonely', 4: 'a = 1 and w > 0 (extra laps)',
            5: 'fast last mover (rho > 8) whose lap is NOT the first opening after a', 6: 'last mover clear at R = 1 (enters the way later)',
            7: 'Ngrid = 1', 8: 'window |x| > 1 with class inequalities all true but landing != R1', 9: 'residue-0 pair with more than one blocker at R = 1 and landing = R1',
            10: 'most moves', 11: 'outside the window: self_clear_at_int_iff prediction differs'}

def qr_hists():
    """parse the Ngrid histograms of quotient_reduction_v1.out for A(16), A(20), A(24)."""
    res = {}
    try:
        txt = open(os.path.join(HERE, 'quotient_reduction_v1.out')).read().split('\n')
    except OSError:
        return res
    cur = None
    for ln in txt:
        if ln.startswith('POPULATION A('):
            cur = int(ln.split('(')[1].split(')')[0])
        if cur and 'histogram of Ngrid:' in ln:
            d = {}
            for tok in ln.split('histogram of Ngrid:')[1].split():
                k, v = tok.split(':'); d[int(k)] = int(v)
            res[cur] = d; cur = None
    return res

def report(title, M, qr=None):
    C = M['C']; H = M['H']
    t = C['total']
    print('\n' + '=' * 118)
    print(title)
    print('=' * 118)
    print('sets %d (sets on which a cascade hit the move limit: %d); most moves %d; total moves %d' % (t, C['nofix'], C['maxMoves'], C['nmoves']))
    print('[OBS] landing R* = 1: %s;  R* an integer > 1: %s;  R* NOT an integer (the hypothesis hnon of displaced_landing): %s' % (
        pct(C['land1'], t), pct(C['landInt'], t), pct(C['landNonInt'], t)))
    print('[OBS] of the non-integer landings: no lonely integer instant in 1..8m (a over one full period 1..8m): %s;  some integer instant is lonely (a later one): %s' % (
        pct(C['dispNoInt'], C['landNonInt']), pct(C['nonIntButInt'], C['landNonInt'])))
    print('--- (C) chain  [final_landing, landing_step, setter_opening, consecutive_difference]  violations must be 0')
    print('    R_{n+1} rho_s = 8 z + 1: %d;  (R_{n+1}-R_n) rho = 1 - delta: %d;  setter blocked at R_n: %d;  R_n < R_{n+1}: %d  (over %d moves)' % (
        C['chainIdViol'], C['chainDiffViol'], C['chainBlockedViol'], C['chainMonoViol'], C['nmoves']))
    print('    number of moves of the cascade: ' + ' '.join('%d:%d' % kv for kv in sorted(H['hMoves'].items())))
    L = C['landNonInt']
    print('--- (D) displaced landing (R* not an integer; a = floor R* >= 1)  [displaced_landing]  violations must be 0')
    print('    a = floor R*: ' + ' '.join('%d:%d' % kv for kv in sorted(H['hA'].items())))
    print('    identity (R*-a) rho_j = Ngrid - a e_j [displaced_identity]: %d;  a e < Ngrid < idx+(a+1)e [gridPart_bounds]: %d;  Ngrid = 1 - a idx mod 8 [gridPart_emod]: %d' % (
        C['idViol'], C['boundViol'], C['modViol']))
    print('    quotient shift Ngrid(a,idx,z) = Ngrid(a,ridx,z - a quo) [gridPart_quo_shift]: %d;  R*(dRed/m) = 8(z-a quo)+1 - 8 quo (R*-a) [reduced_reading_at_landing]: %d' % (
        C['quoViol'], C['redViol']))
    print('    ties at the last move (two setters with the same opening): %d' % C['lastTies'])
    print('    PREVIOUS landing R0 = R_{N-1}, u = R0 - a: window rho u + a e < Ngrid < rho u + a e + 2 [gridPart_prev_window]: violations %d;  R0 < a (the last move crosses a): %d;  R0 >= a: %d' % (
        C['prevWinViol'], C['prevBelowA'], C['prevAtOrAboveA']))
    print('    EVERY step of every chain, a = 1: window violations %d;  first step (R0 = 1): Ngrid not in {0,1,2} or 0 with e >= 0 or 2 with e <= 0 [gridPart_first_step]: %d' % (
        C['stepWinViol'], C['stepFirstViol']))
    print('       Ngrid_n(1) over all steps: ' + ' '.join('%d:%d' % kv for kv in sorted(H['hStepN'].items())))
    print('    histogram of Ngrid (a = floor R*): ' + ' '.join('%d:%d' % kv for kv in sorted(H['hN'].items())))
    print('    Ngrid < 0: %d;  = 0: %d;  = 1: %d;  in 2..7: %d;  >= 8: %d' % (C['Nneg'], C['Nzero'], C['None'], C['N2to7'], C['Nge8']))
    print('    Ngrid mod 8: ' + ' '.join('%d:%d' % kv for kv in sorted(H['hNres'].items())))
    print('    Ngrid = 0 [gridPart_zero]: %d sets; violations of (a idx = 1 mod 8 and e < 0): %d;  ridx of the last mover there: %s' % (
        C['N0'], C['N0viol'], ' '.join('%d:%d' % kv for kv in sorted(H['hNzeroRidx'].items()))))
    print('    Ngrid = 1 [gridPart_one]: %d sets; violations of (8 | a idx): %d;  a odd and idx not = 0 mod 8: %d' % (C['N1'], C['N1viol'], C['N1oddviol']))
    print('    ridx of the last mover: ' + ' '.join('%d:%d' % kv for kv in sorted(H['hRidxLast'].items())))
    print('    SLOW last mover (rho <= 8): %d;  lap != floor((a rho - 1)/8) + 1 [lap_first_opening]: %d;  of these a = 1: %d, with Ngrid != (1-idx) mod 8 or (idx = 1 mod 8 and e >= 0) [gridPart_one_slow]: %d' % (
        C['slow'], C['slowLapViol'], C['slowOne'], C['slowOneViol']))
    print('    FAST last mover (rho > 8): %d;  lap = first opening after a: %d;  lap NOT the first opening after a: %d   (all last movers: not first %d)' % (
        C['fast'], C['fastLapFirst'], C['fastLapNotFirst'], C['lapFirstAllViol']))
    print('    a = 1: %d sets;  Ngrid != (1-idx) mod 8 + 8w with w >= 0 [gridPart_one_laps]: %d;  Ngrid >= idx + 2e: %d;  w histogram: %s' % (
        C['aOne'], C['oneLapsViol'], C['oneBoundViol'], ' '.join('%d:%d' % kv for kv in sorted(H['hW'].items()))))
    print('    last mover at the integer a [self_clear_at_int_iff]: window |e a| <= 1: %d sets, prediction wrong: %d;  outside the window: %d sets' % (
        C['selfWin'], C['selfWinViol'], C['selfNoWin']))
    print('       clear at a: %d;  blocked at a: %d;  by Ngrid mod 8:  =1: %d sets (blocked %d);  =0: %d (blocked %d);  =2: %d (blocked %d);  other: %d (blocked %d)' % (
        C['selfClear'], C['selfBlocked'], C['selfN1'], C['selfBlockedN1'], C['selfN0'], C['selfBlockedN0'], C['selfN2'], C['selfBlockedN2'],
        C['selfOther'], C['selfBlockedOther']))
    print('    last mover blocked at R = 1: %d;  clear at R = 1 (it enters the way after the cascade has moved): %d' % (C['lastBlockedAt1'], C['lastNotBlockedAt1']))
    if qr is not None:
        mine = dict(H['hNodd'])
        print('    QR cross-check: sets with no lonely odd integer and non-integer landing: %d;  identity violations with the nearest odd a: %d' % (C['QRdisp'], C['QRidViol']))
        print('       Ngrid histogram with the nearest odd integer a (non-integer landings only): ' + ' '.join('%d:%d' % kv for kv in sorted(mine.items())))
        if qr:
            diff = {k: qr[k] - mine.get(k, 0) for k in qr if qr[k] != mine.get(k, 0)}
            extra = {k: mine[k] for k in mine if k not in qr}
            ev = dict(H['hNoddEven'])
            print('       quotient_reduction_v1.out histogram minus mine: %s (extra in mine: %s);  the sets with an EVEN integer landing and no lonely odd integer (%d), with a = R* - 1: %s' % (
                diff, extra, C['evenIntNoOdd'], ev))
            print('       quotient_reduction_v1.out histogram = mine + even-integer-landing sets: %s' % (diff == ev and not extra))
    print('--- (F) family of a residue-0 reading  [landing_R1_iff_lonely, first_move_residue_zero, family_landing_iff, family_landing_classes]')
    print('    pairs (set, reading d0 with ridx = 8): %d;  landing = R1(d0): %d;  (landing = R1) != (lonely at R1): %d  [violations must be 0; no only-blocker hypothesis]' % (
        C['famPairs'], C['famLand'], C['famIffViol']))
    print('    ANY reading blocked at R = 1, opening (8 z1 + 1)/rho [landing_opening_iff_lonely]: pairs %d, landing = that opening: %d, (landing = opening) != (lonely there): %d  [must be 0]' % (
        C['genPairs'], C['genLand'], C['genIffViol']))
    print('       by ridx of the blocked reading: pairs ' + ' '.join('%d:%d' % kv for kv in sorted(H['hGenPairs'].items())) +
          ';  landing = opening: ' + ' '.join('%d:%d' % kv for kv in sorted(H['hGenLand'].items())))
    print('    pairs with >= 2 blockers at R = 1 and landing = R1(d0): %d  (so the only-blocker hypothesis is not necessary); in those, the first cascade move is not R1: %d' % (
        C['famNonUniqueLand'], C['famNonUniqueMoveNotR1']))
    print('    d0 the ONLY blocker at R = 1: %d;  first cascade move != R1: %d  [must be 0];  landing = R1: %d;  second move (landing != R1): %d' % (
        C['uniq'], C['uniqFirstMoveViol'], C['uniqLand'], C['uniqSecond']))
    print('       Win formula (ridx + x_d) vs the actual state of every other reading at R1: disagreements %d  [must be 0]' % C['uniqFormViol'])
    print('       window |x_d| <= 1 for all other readings: %d sets;  not for all: %d sets' % (C['uniqWinOK'], C['uniqWinBad']))
    print('       class inequalities vs actual state, readings inside the window: disagreements %d  [must be 0]' % C['uniqClassViol'])
    print('       window violated, all class inequalities true, yet landing != R1: %d sets  (window REQUIRED)' % C['uniqBadClassWrong'])
    sec = H['hSecond']
    print('       second move: the first other reading blocked at R1, by (ridx, quo>0, e<0): ' + ' '.join(
        '(%d,%d,%d):%d' % (k // 4, (k // 2) % 2, k % 2, v) for k, v in sorted(sec.items())) + ';  two or more blocked at R1: %d' % C['uniqMultiBlocked'])
    print('--- witnesses (first set found; y_0..y_6):')
    for k in sorted(M['W']):
        print('    %-80s %s' % (WITNAMES[k], M['W'][k]))

# ---------------------------------------------------------------------------------------------------------------
# Independent Fraction reference (aggregates of the kernel on A(16), A(20))
# ---------------------------------------------------------------------------------------------------------------
LIMIT = 100000

def fr_round(x):
    return (x + F(1, 2)).__floor__()

def f_cascade(ys, m):
    R = F(1); chain = []
    for _ in range(LIMIT):
        best = None
        for j, y in enumerate(ys):
            x = F(y, m) * R
            z = fr_round(x / 8)
            if abs(x - 8 * z) < 1:
                nx = F(8 * z + 1) * m / y
                if best is None or nx > best[0]: best = (nx, j, z)
        if best is None: return R, chain
        chain.append((best[1], best[2], R)); R = best[0]
    return None, None

def f_blocked(y, m, R):
    x = F(y, m) * R
    return abs(x - 8 * fr_round(x / 8)) < 1

def reference(N):
    tot = 0; land1 = landInt = landNon = 0; hist = Counter(); uniq = uniqLand = famPairs = famLand = 0; nz = 0; slowOne = 0
    for S in combinations(range(1, N + 1), 7):
        g = 0
        for y in S: g = gcd(g, y)
        if g != 1: continue
        tot += 1; m = S[0]
        R, chain = f_cascade(S, m)
        assert R is not None
        idx = [fr_round(F(y, m)) for y in S]; e = [F(y, m) - i for y, i in zip(S, idx)]
        ridx = [(i - 1) % 8 + 1 for i in idx]; quo = [(i - 1) // 8 for i in idx]
        if R == 1: land1 += 1
        elif R.denominator == 1: landInt += 1
        else:
            landNon += 1
            a = R.__floor__(); j, z, _ = chain[-1]
            Ng = 8 * z + 1 - a * idx[j]
            assert (R - a) * F(S[j], m) == Ng - a * e[j]
            hist[Ng] += 1
            if Ng == 0: nz += 1
            if S[j] <= 8 * m and a == 1:
                slowOne += 1
                assert Ng == (1 - idx[j]) % 8
        bl = [f_blocked(y, m, F(1)) for y in S]
        for d0 in range(7):
            if ridx[d0] != 8: continue
            R1 = 1 + (1 - e[d0]) / F(S[d0], m)
            lon = all(not f_blocked(y, m, R1) for y in S)
            famPairs += 1
            if R == R1: famLand += 1
            assert lon == (R == R1)
            if sum(bl) == 1 and bl[d0]:
                uniq += 1
                if R == R1: uniqLand += 1
                assert chain[0][2] == 1 and chain[0][0] == d0
    return dict(tot=tot, land1=land1, landInt=landInt, landNon=landNon, hist=dict(hist), uniq=uniq, uniqLand=uniqLand,
                famPairs=famPairs, famLand=famLand, Nzero=nz, slowOne=slowOne)

def compare_reference(N, M):
    t0 = time.time()
    r = reference(N)
    C = M['C']
    ok = (r['tot'] == C['total'] and r['land1'] == C['land1'] and r['landInt'] == C['landInt'] and r['landNon'] == C['landNonInt'] and
          r['uniq'] == C['uniq'] and r['uniqLand'] == C['uniqLand'] and r['famPairs'] == C['famPairs'] and r['famLand'] == C['famLand'] and
          r['Nzero'] == C['Nzero'] and r['slowOne'] == C['slowOne'] and r['hist'] == dict(M['H']['hN']))
    print('Fraction reference on A(%d): sets %d, R*=1 %d, integer %d, non-integer %d, d0-only-blocker %d (landing R1: %d), pairs %d (landing R1: %d), Ngrid=0: %d,' % (
        N, r['tot'], r['land1'], r['landInt'], r['landNon'], r['uniq'], r['uniqLand'], r['famPairs'], r['famLand'], r['Nzero']))
    print('     Ngrid histogram identical to the C kernel: %s;  every aggregate identical: %s;  identities asserted inside the reference: yes  (%.0f s)' % (
        r['hist'] == dict(M['H']['hN']), ok, time.time() - t0))
    assert ok

# ---------------------------------------------------------------------------------------------------------------
# Families
# ---------------------------------------------------------------------------------------------------------------
def family_tables():
    print('\n' + '=' * 118)
    print('FAMILIES (exact Fractions)  [landing_family in QuotientReduction; landing_R1_iff_lonely; family_landing_iff; second_move_example]')
    print('=' * 118)
    rows = {}
    for Y in range(7, 801):
        rows[Y] = f_cascade((1, 2, 3, 4, 5, 6, Y), 1)
    bad = sum(1 for k in range(1, 101) if rows[8 * k][0] != 1 + F(1, 8 * k))
    print('{1,2,3,4,5,6,Y}, Y = 7..800: Y = 0 mod 8 (100 values): landing = 1 + 1/Y for every one: violations %d  (R1 = 1 + (1 - e0)/rho0, e0 = 0; a = 1, Ngrid = 1, lap k = Y/8)' % bad)
    for r in range(1, 8):
        L = [Y for Y in rows if Y % 8 == r]
        print('   Y = %d mod 8: %d values, landing = 1 in %d (residues of 1..6 and r are distinct mod 8: the grid instant R = 1 is lonely)' % (
            r, len(L), sum(1 for Y in L if rows[Y][0] == 1)))
    print('   Y = 8k, last mover and lap for k = 1..6: ' + '; '.join('Y=%d: R*=%s lap %d' % (8 * k, rows[8 * k][0], rows[8 * k][1][-1][1]) for k in range(1, 7)))
    # deviation family {1,..,6, 8k+e}
    print('\n{1,2,3,4,5,6, 8k + e}, e = p/q in [-1/2, 1/2), q <= 24, k = 1, 2, 3 (scaled by q: (q,2q,..,6q, 8kq+p)); d0 = 8k+e has ridx 8, R1 = 1 + (1-e)/(8k+e).')
    print('Prediction (family_landing_iff, only the reading 6 can fail): landing = R1  iff  k >= 2 or e >= -2/7   [reading 6: x = 6 (R1 - 1) <= 1].')
    tot = viol = 0; exc = []
    seen = set()
    for q in range(1, 25):
        for pnum in range(-(q // 2) - 1, q // 2 + 2):
            e = F(pnum, q)
            if not (F(-1, 2) <= e < F(1, 2)) or e in seen: continue
            seen.add(e)
            for k in (1, 2, 3):
                qq = e.denominator; pp = e.numerator
                ys = tuple(qq * i for i in range(1, 7)) + (8 * k * qq + pp,)
                R, chain = f_cascade(ys, qq)
                R1 = 1 + (1 - e) / (8 * k + e)
                pred = (k >= 2) or (e >= F(-2, 7))
                tot += 1
                if (R == R1) != pred: viol += 1
                if R != R1: exc.append((k, e, R, len(chain)))
    print('[OBS] cases %d (distinct e: %d x 3 values of k);  (landing = R1) != prediction: %d;  landing != R1 in %d cases, all with k = 1: %s' % (
        tot, len(seen), viol, len(exc), all(k == 1 for k, _, _, _ in exc)))
    ex1 = sorted([(e, R, n) for k, e, R, n in exc if k == 1])[:6]
    print('   examples (k = 1; e, landing, moves): ' + '; '.join('e=%s: R*=%s (%d moves)' % (e, R, n) for e, R, n in ex1))
    print('   largest e with landing != R1 (k = 1): %s  (-2/7 = %s excluded: at e = -2/7 the reading 6 sits at 7: clear, the closed condition)' % (max(e for k, e, _, _ in exc), F(-2, 7)))
    # second move
    print('\n{1,2,3,4,5,7,8k}  (second move: the residue-7 reading 7, e = 0, enters its zone at R1 = 1 + 1/(8k)):')
    out = []
    for k in range(1, 61):
        R, chain = f_cascade((1, 2, 3, 4, 5, 7, 8 * k), 1)
        out.append((k, R, len(chain)))
    print('[OBS] k = 1..60: R* = 9/7 for %d values of k; the others: %s' % (
        sum(1 for k, R, n in out if R == F(9, 7)), ', '.join('k=%d: %s' % (k, R) for k, R, n in out if R != F(9, 7))))
    print('   (the exceptions are k = 0 mod 7: 8k * 9/7 is then a multiple of 8, the residue-0 reading k blocks at 9/7)')

def main():
    t0 = time.time()
    build()
    print('DISPLACED LANDING OF THE CASCADE CHAIN: exact-arithmetic data [OBS] (task BD).  Kernel source embedded; compiled with cc at run time.')
    qr = qr_hists()
    results = {}
    for N in (16, 20, 24):
        results[N] = run_pop('A', N, 10)
        report('POPULATION A(%d): 7-subsets of {1..%d}, gcd 1' % (N, N), results[N], qr.get(N, {}))
    resQ3 = run_pop('Q', 3, 10)
    report('POPULATION Q = 3: every 7-subset of {3,..,36} whose elements are not all multiples of 3 (the real_case_v1.py population)', resQ3, None)
    print('\n' + '=' * 118)
    print('CROSS-CHECK against an independent Fraction implementation (framework definitions: InWay, nextOpening, largest opening)')
    print('=' * 118)
    for N in (16, 20):
        compare_reference(N, results[N])
    family_tables()
    print('\nelapsed %.0f s' % (time.time() - t0))
    shutil.rmtree(WORK, ignore_errors=True)

if __name__ == '__main__':
    main()
