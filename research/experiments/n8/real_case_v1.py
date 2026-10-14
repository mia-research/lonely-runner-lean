"""Task AO: the real case.  Exact enumeration of landings of rational disparity sets with non-integer ratios.

Disparity sets are 7-subsets D of {a/Q : a integer, 1 <= a/Q <= HI}; D has PRIMITIVE DENOMINATOR Q iff Q is the least
positive integer q with q*D contained in the integers.  For Q prime this is: some element of D is not an integer, i.e.
the numerators a_i are not all divisible by Q (gcd of the numerators not divisible by Q).  The cascade is scale
covariant (d -> c d sends t -> t/c and R = 8 d_min t is unchanged), so D is cascade-equivalent to the integer set of
its numerators; the populations below are the integer sets {a_i} with a_i/min a_i <= HI and a_i not all multiples of Q.
That equivalence is why 'rational' is not a new case for the cascade; what these populations add is the range of
ratios d/d_min, and the real case (irrational ratios) is treated by symbolic statements in Fresh/RealCase.lean.

The cascade (framework definitions): InWay d t iff distInt(d t) < 1/8; nextOpening d t = (ceil(d t - 1/8) + 1/8)/d;
a move goes to the largest next opening among the runners in the way; start t0 = 1/(8 d_min); the landing is the fixed
point.  The kernel (C, int64, no floating point) runs it on the numerators with time tau = t/Q: state tau = n/(8x).
Two independent Fraction references (the framework cascade, and the least clear opening by the congruence
x <= d(8k+1) mod 8x <= 7x) are compared with the kernel on full small populations and on deterministic subsets.

Every count is [OBS] (provisional: counting tool); nothing here is offered as an argument (rule 7).
Usage: python3 real_case_v1.py        (runs everything; about 30 minutes; needs gcc)
"""
import os, sys, subprocess, tempfile, shutil, time
from fractions import Fraction as F
from math import comb, floor, ceil, gcd
from collections import defaultdict

C_SOURCE = r'''/* Exact integer kernel for real_case_v1.py (task AO).  Disparities are a_i/Q (a_i integers, a_i/Q in [1,hi]); the
   cascade is run on the integer numerators with time tau = t/Q (reading d t = a tau); R = 8 d_min t = 8 a_min tau.
   All arithmetic is int64; no floating point.  Modes: stats | dump. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll;
typedef unsigned __int128 u128;
static ll gcdll(ll a, ll b){ while(b){ ll t=a%b; a=b; b=t;} return a<0?-a:a; }
static int Q, HI, AMIN, AMAX, MODE_PRIM; static ll A0MAX=1000000; /* MODE_PRIM=1: primitive denominator Q ; 0: gcd 1 */
static ll FIRSTSET[8]; 
typedef struct { ll n, x; int rank, lap, nopen, ntouch, nmoves, fs_rank, fs_lap, setter_rank_final, finalset_in_open, nforb, smallest_forb_rank, first_setter_is_smallest_forb; } Res;

static void cascade(const ll *a, Res *R){
  ll n = 1, x = a[0]; int moves = 0; int first = 1;
  R->nforb = 0; R->smallest_forb_rank = -1; R->first_setter_is_smallest_forb = -1; R->fs_rank=-1; R->fs_lap=-1;
  int last_rank = 0; ll last_lap = 0;
  for(;;){
    ll m = 8*x; ll bn=0, by=1; int brank=-1; ll bj=0; int anyway=0; int smallest=-1;
    for(int i=0;i<7;i++){
      ll y=a[i]; ll r=(y*n)%m; ll dist = r < m-r ? r : m-r;
      if(dist < x){
        anyway=1; if(smallest<0) smallest=i;
        ll num = y*n - x; ll j = (num + m - 1)/m; ll nn = 8*j+1; /* tau' = nn/(8y) */
        if(brank<0 || nn*by > bn*y){ bn=nn; by=y; brank=i; bj=j; }
      }
    }
    if(!anyway) break;
    if(first){ R->nforb=0; for(int i=0;i<7;i++){ ll y=a[i]; ll r=(y*n)%m; ll dist = r < m-r ? r : m-r; if(dist<x) R->nforb++; }
      R->smallest_forb_rank=smallest; R->fs_rank=brank; R->fs_lap=(int)bj; R->first_setter_is_smallest_forb = (brank==smallest); first=0; }
    n=bn; x=by; moves++; last_rank=brank; last_lap=bj;
  }
  R->n=n; R->x=x; R->nmoves=moves; R->setter_rank_final = moves? last_rank : 0;
  ll m=8*x; R->nopen=0; R->ntouch=0; R->rank=-1;
  for(int i=0;i<7;i++){ ll r=(a[i]*n)%m; if(r==x){ R->nopen++; if(R->rank<0){ R->rank=i; R->lap=(int)((a[i]*n - x)/m); } } else if(r==7*x) R->ntouch++; }
  /* final setter in openers? */
  if(moves){ ll r=(a[last_rank]*n)%m; R->finalset_in_open = (r==x) && ((a[last_rank]*n-x)/m==last_lap); } else R->finalset_in_open = (R->rank==0 && R->lap==0);
}

static int filt(const ll *a){
  ll g=0; for(int i=0;i<7;i++) g=gcdll(g,a[i]);
  if(MODE_PRIM) return (g % Q)!=0;   /* some a_i not divisible by Q <=> the numerators' gcd is not divisible by Q (Q prime) */
  return g==1;
}

/* pattern key */
static u128 patkey(const ll *a){
  u128 k=0; ll M=8*a[0];
  for(int i=1;i<7;i++){ ll r=a[i]%M; ll g=gcdll(r,a[0]); ll num=r/g, den=a[0]/g; /* r=0 => g=a0,num=0,den=1 */
    k = (k<<17) | ((u128)((den<<10)|num)); }
  return k;
}
static inline uint64_t h128(u128 k){ uint64_t lo=(uint64_t)k, hi=(uint64_t)(k>>64); uint64_t h=lo*0x9E3779B97F4A7C15ULL ^ (hi+0x7F4A7C15ULL)*0xC2B2AE3D27D4EB4FULL; h^=h>>29; h*=0xBF58476D1CE4E5B9ULL; h^=h>>32; return h; }

static u128 *tkeys; static uint16_t *tval; static uint64_t tmask;
static ll npat=0, nconf_pat=0, nconf_ins=0; static u128 conf_keys[8]; static int nck=0;

int main(int argc, char**argv){
  if(argc<5){ fprintf(stderr,"usage: kernel mode Q HI primflag [tablebits]\n"); return 2; }
  const char*mode=argv[1]; Q=atoi(argv[2]); HI=atoi(argv[3]); MODE_PRIM=atoi(argv[4]); int tbits = argc>5? atoi(argv[5]):0; if(argc>6) A0MAX=atoll(argv[6]);
  AMIN=Q; AMAX=Q*HI; if(argc>7) AMAX=atoi(argv[7]); int V=AMAX-AMIN+1; int dump = !strcmp(mode,"dump");
  if(tbits){ tmask=((uint64_t)1<<tbits)-1; tkeys=calloc((size_t)1<<tbits,sizeof(u128)); tval=calloc((size_t)1<<tbits,sizeof(uint16_t)); if(!tkeys||!tval){fprintf(stderr,"alloc\n");return 3;} }
  ll total=0, nties=0, ntouch=0, nboth=0, neither=0, neither_t=0, only_tie=0, only_touch=0;
  ll lap0=0, win1=0, win_mid=0, win_hi=0, rmaxn=0, rmaxd=1; ll rmin_hi_n=0, rmin_hi_d=1;
  ll cls[7][128]; memset(cls,0,sizeof cls); ll clsT[7][128]; memset(clsT,0,sizeof clsT);
  ll expl[5]; memset(expl,0,sizeof expl); /* first working odd a: index 1,3,5,7 ; 0 none */
  ll expl_any=0, expl_none=0, expl_none_lap0=0; ll land_is_odd=0; ll land_is_odd_works=0;
  ll nforb_sets=0, fs_not_smallest=0, fs_ex_n=0; ll fs_ex[6][7]; ll land_lap0_noforb_mismatch=0;
  ll fin_not_open=0, rank1_lap_pos=0, gcd1_sets=0, gcd1_bound_viol=0;
  ll lapabove0_with_forb=0;
  ll r9=0, rgate=0; ll fsr_n=0, fsr_d=1; int fsr_set=0; ll hir_n=0, hir_d=1; int hir_set=0; ll ex7n=0; ll exhi[6][7]; int exhi_n=0; ll exr1[6][7]; int exr1_n=0; ll exmax[7]; 
  int idx[7]; ll a[7];
  /* iterate combinations */
  for(idx[0]=0; idx[0]<V-6 && AMIN+idx[0]<=A0MAX; idx[0]++) for(idx[1]=idx[0]+1; idx[1]<V-5; idx[1]++) for(idx[2]=idx[1]+1; idx[2]<V-4; idx[2]++)
  for(idx[3]=idx[2]+1; idx[3]<V-3; idx[3]++) for(idx[4]=idx[3]+1; idx[4]<V-2; idx[4]++) for(idx[5]=idx[4]+1; idx[5]<V-1; idx[5]++)
  for(idx[6]=idx[5]+1; idx[6]<V; idx[6]++){
    for(int i=0;i<7;i++) a[i]=AMIN+idx[i];
    if(!filt(a)) continue;
    Res R; cascade(a,&R); total++;
    if(dump){ printf("%lld %lld %lld %lld %lld %lld %lld %lld %lld %d %d %d\n",a[0],a[1],a[2],a[3],a[4],a[5],a[6],R.n,R.x,R.nopen,R.ntouch,R.rank+1); continue; }
    int tie = R.nopen>=2, tou = R.ntouch>=1;
    if(tie) nties++; if(tou) ntouch++; if(tie&&tou) nboth++; if(tie&&!tou) only_tie++; if(!tie&&tou) only_touch++; if(!tie&&!tou) neither++;
    /* R* = a0 n / x */
    ll Rn=a[0]*R.n, Rd=R.x;
    if(Rn==Rd) win1++; else if(Rn<=7*Rd) win_mid++; else win_hi++;
    if(Rn==9*Rd) r9++; if(Rn>7*Rd && Rn<9*Rd) rgate++;
    if(Rn>7*Rd){ if(!hir_set || a[6]*hir_d < hir_n*a[0]){ hir_n=a[6]; hir_d=a[0]; hir_set=1; } }
    if(Rn*rmaxd > rmaxn*Rd){ rmaxn=Rn; rmaxd=Rd; for(int i=0;i<7;i++) exmax[i]=a[i]; }
    if(Rn>7*Rd && exhi_n<6){ for(int i=0;i<7;i++) exhi[exhi_n][i]=a[i]; exhi_n++; }
    if(R.rank==0 && R.lap>0 && exr1_n<6){ for(int i=0;i<7;i++) exr1[exr1_n][i]=a[i]; exr1_n++; }
    if(R.rank<0){ fprintf(stderr,"no opener at landing?\n"); return 4; }
    if(R.lap>=128){ fprintf(stderr,"lap too big\n"); return 5; }
    cls[R.rank][R.lap]++; if(tie||tou) clsT[R.rank][R.lap]++;
    if(R.rank==0 && R.lap>0) rank1_lap_pos++;
    if(!R.finalset_in_open) fin_not_open++;
    if(R.lap>0 || R.nmoves>0) {} 
    /* lap0 landing iff no forbidden */
    if((R.nforb==0) != (R.n==1 && R.x==a[0])) land_lap0_noforb_mismatch++;
    if(R.nforb>0){ nforb_sets++; if(!R.first_setter_is_smallest_forb){ fs_not_smallest++; if(!fsr_set || a[6]*fsr_d < fsr_n*a[0]){ fsr_n=a[6]; fsr_d=a[0]; fsr_set=1; } if(fs_ex_n<6){ for(int i=0;i<7;i++) fs_ex[fs_ex_n][i]=a[i]; fs_ex_n++; } } }
    /* explicit instants */
    int first=0; for(int ao=1; ao<=7; ao+=2){ int ok=1; for(int i=0;i<7;i++){ ll r=(ao*a[i])%(8*a[0]); if(r<a[0]||r>7*a[0]){ok=0;break;} } if(ok&&!first) first=ao; }
    if(first){ expl[first/2+1-1+0]++; expl_any++; } else { expl_none++; if(R.n==1&&R.x==a[0]) expl_none_lap0++; }
    if(Rd && Rn%Rd==0){ ll v=Rn/Rd; if(v==1||v==3||v==5||v==7) land_is_odd++; }
    { ll g=0; for(int i=0;i<7;i++) g=gcdll(g,a[i]); if(g==1){ gcd1_sets++; if(R.n > 4*R.x) gcd1_bound_viol++; } }
    if(tbits){
      u128 k=patkey(a); uint16_t cv=(uint16_t)(1+R.rank*128+R.lap); uint64_t h=h128(k)&tmask;
      for(;;){ if(tval[h]==0){ tkeys[h]=k; tval[h]=cv; npat++; break; }
        if(tkeys[h]==k){ if((tval[h]&0x7fff)!=cv){ nconf_ins++; if(!(tval[h]&0x8000)){ tval[h]|=0x8000; nconf_pat++; if(nck<8) conf_keys[nck++]=k; } } break; }
        h=(h+1)&tmask; }
    }
  }
  if(dump) return 0;
  printf("TOTAL %lld\nTIES %lld\nTOUCH %lld\nBOTH %lld\nONLY_TIE %lld\nONLY_TOUCH %lld\nNEITHER %lld\n",total,nties,ntouch,nboth,only_tie,only_touch,neither);
  printf("R1 %lld\nRMID %lld\nRHI %lld\nRMAX %lld/%lld\n",win1,win_mid,win_hi,rmaxn,rmaxd);
  for(int r=0;r<7;r++) for(int k=0;k<128;k++) if(cls[r][k]) printf("CLASS %d %d %lld %lld\n",r+1,k,cls[r][k],clsT[r][k]);
  printf("EXPL_FIRST1 %lld\nEXPL_FIRST3 %lld\nEXPL_FIRST5 %lld\nEXPL_FIRST7 %lld\nEXPL_ANY %lld\nEXPL_NONE %lld\nEXPL_NONE_LAP0 %lld\nLAND_IS_ODD %lld\n",expl[0],expl[1],expl[2],expl[3],expl_any,expl_none,expl_none_lap0,land_is_odd);
  printf("NFORB_SETS %lld\nFS_NOT_SMALLEST %lld\nLAP0_IFF_NOFORB_MISMATCH %lld\nFINAL_NOT_OPEN %lld\nRANK1_LAP_POS %lld\nGCD1_SETS %lld\nGCD1_BOUND_VIOL %lld\n",nforb_sets,fs_not_smallest,land_lap0_noforb_mismatch,fin_not_open,rank1_lap_pos,gcd1_sets,gcd1_bound_viol);
  for(int e=0;e<fs_ex_n;e++){ printf("FSEX"); for(int i=0;i<7;i++) printf(" %lld",fs_ex[e][i]); printf("\n"); }
  printf("R9 %lld\nRGATE %lld\n",r9,rgate); if(fsr_set) printf("FSMINRATIO %lld/%lld\n",fsr_n,fsr_d); if(hir_set) printf("HIMINRATIO %lld/%lld\n",hir_n,hir_d);
  printf("EXMAX"); for(int i=0;i<7;i++) printf(" %lld",exmax[i]); printf("\n");
  for(int e=0;e<exhi_n;e++){ printf("EXHI"); for(int i=0;i<7;i++) printf(" %lld",exhi[e][i]); printf("\n"); }
  for(int e=0;e<exr1_n;e++){ printf("EXR1"); for(int i=0;i<7;i++) printf(" %lld",exr1[e][i]); printf("\n"); }
  if(tbits){ printf("PATTERNS %lld\nCONFLICT_PATTERNS %lld\nCONFLICT_INSERTS %lld\n",npat,nconf_pat,nconf_ins);
    /* pass 2: print up to 6 sets for each of up to 4 conflict keys */
    int show = nck<4?nck:4;
    for(int c=0;c<show;c++){ int printed=0; int seen[16]; int ns=0;
      for(idx[0]=0; idx[0]<V-6 && printed<4 && AMIN+idx[0]<=A0MAX; idx[0]++) for(idx[1]=idx[0]+1; idx[1]<V-5 && printed<4; idx[1]++) for(idx[2]=idx[1]+1; idx[2]<V-4 && printed<4; idx[2]++)
      for(idx[3]=idx[2]+1; idx[3]<V-3 && printed<4; idx[3]++) for(idx[4]=idx[3]+1; idx[4]<V-2 && printed<4; idx[4]++) for(idx[5]=idx[4]+1; idx[5]<V-1 && printed<4; idx[5]++)
      for(idx[6]=idx[5]+1; idx[6]<V && printed<4; idx[6]++){
        for(int i=0;i<7;i++) a[i]=AMIN+idx[i];
        if(!filt(a)) continue; if(patkey(a)!=conf_keys[c]) continue;
        Res R; cascade(a,&R); int cid=R.rank*128+R.lap; int dup=0; for(int q=0;q<ns;q++) if(seen[q]==cid) dup=1;
        if(dup) continue; if(ns<16) seen[ns++]=cid;
        printf("CONFEX %d %lld %lld %lld %lld %lld %lld %lld  n=%lld x=%lld rank=%d lap=%d\n",c,a[0],a[1],a[2],a[3],a[4],a[5],a[6],R.n,R.x,R.rank+1,R.lap); printed++; }
    }
  }
  return 0;
}
'''

WORK = tempfile.mkdtemp(prefix="real_case_")
SRC = os.path.join(WORK, "rc_kernel.c")
BIN = os.path.join(WORK, "rc_kernel")
open(SRC, "w").write(C_SOURCE)
subprocess.check_call(["gcc", "-O2", "-o", BIN, SRC])

def kernel(mode, Q, HI, prim, tbits=0, a0max=None, amax=None):
    args = [BIN, mode, str(Q), str(HI), str(prim), str(tbits)]
    if a0max is not None or amax is not None:
        args.append(str(a0max if a0max is not None else 10**9))
    if amax is not None:
        args.append(str(amax))
    return subprocess.run(args, capture_output=True, text=True, check=True).stdout

def pr(*a): print(*a, flush=True)
def frs(x): return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"
def pct(a, b, digits=4):
    """a/b as an exact fraction with a decimal rendering by integer arithmetic (no floating point)."""
    if b == 0: return "n/a"
    q = a * 10**(digits + 2) // b
    s = f"{q // 10**digits}.{q % 10**digits:0{digits}d}"
    return f"{a}/{b} = {s}%"

# ---------------------------------------------------------------- Fraction references
def dist_int(x):
    f = x - floor(x)
    return min(f, 1 - f)

def ref_cascade(D):
    """Framework cascade on Fractions D (sorted ascending): returns the landing t."""
    t = F(1, 8) / D[0]
    while True:
        inway = [d for d in D if dist_int(d * t) < F(1, 8)]
        if not inway: return t
        t = max((ceil(d * t - F(1, 8)) + F(1, 8)) / d for d in inway)

def ref_openings(D):
    """Least clear opening: independent of the cascade (candidates (8k+1)/(8x), clear iff all d*(8k+1) mod 8x in [x,7x])."""
    best = None
    for x in D:
        for k in range(0, int(x * 40) + 1):
            t = (8 * k + 1) / (8 * x)
            if best is not None and t >= best: break
            if all(F(1, 8) <= dist_int(d * t) for d in D):
                best = t if best is None else min(best, t); break
    return best

def ref_features(D, t):
    op = [i for i, d in enumerate(D) if d * t - floor(d * t) == F(1, 8)]
    en = [i for i, d in enumerate(D) if d * t - floor(d * t) == F(7, 8)]
    return len(op), len(en), (op[0] + 1 if op else None)

def validate(label, Q, HI, prim, a0max=None, amax=None, stride=1, check_openings=True):
    out = kernel("dump", Q, HI, prim, 0, a0max, amax)
    n = 0; bad = 0; badop = 0
    for idx, line in enumerate(out.splitlines()):
        if idx % stride: continue
        v = list(map(int, line.split()))
        a = v[:7]; nn, x, nopen, ntouch, rank = v[7:12]
        D = [F(ai, Q) for ai in a]
        t = ref_cascade(D)
        ok = (t == F(Q * nn, 8 * x)) and ref_features(D, t) == (nopen, ntouch, rank)
        if not ok: bad += 1
        if check_openings and idx % (stride * 7) == 0:
            if ref_openings(D) != t: badop += 1
        n += 1
    pr(f"[validation] {label}: kernel vs Fraction cascade on {n} sets (every {stride}th of the enumeration): "
       f"mismatches {bad}; vs least-clear-opening on every 7th of these: mismatches {badop}")
    return bad + badop

# ---------------------------------------------------------------- parse and report
def parse(out):
    d = {"CLASS": [], "FSEX": [], "EXHI": [], "EXR1": [], "CONFEX": []}
    for line in out.splitlines():
        p = line.split()
        if not p: continue
        k = p[0]
        if k == "CLASS": d["CLASS"].append((int(p[1]), int(p[2]), int(p[3]), int(p[4])))
        elif k in ("FSEX", "EXHI", "EXR1"): d[k].append(list(map(int, p[1:8])))
        elif k == "EXMAX": d[k] = list(map(int, p[1:8]))
        elif k == "CONFEX": d[k].append(line)
        elif k in ("RMAX", "FSMINRATIO", "HIMINRATIO"): a, b = p[1].split("/"); d[k] = F(int(a), int(b))
        else: d[k] = int(p[1])
    return d

def pset(a, Q):
    return "{" + ", ".join(frs(F(x, Q)) for x in a) + "}"

def report(title, Q, d, tbl, extra=""):
    T = d["TOTAL"]
    pr("\n" + "=" * 110 + f"\nPOPULATION {title}\n{extra}" + "=" * 110)
    pr(f"sets: {T}")
    pr(f"[OBS] ties (two or more runners at exactly 1/8 past a lap line at the landing): {pct(d['TIES'], T)}")
    pr(f"[OBS] touches (a runner at exactly 7/8 at the landing: the landing cell is a single point): {pct(d['TOUCH'], T)}")
    pr(f"[OBS] tie and touch: {d['BOTH']};  tie only: {d['ONLY_TIE']};  touch only: {d['ONLY_TOUCH']};  neither: {d['NEITHER']}")
    pr(f"[OBS] tie or touch (the commensurable coincidences): {pct(d['TIES'] + d['TOUCH'] - d['BOTH'], T)}")
    inwin = d["R1"] + d["RMID"]
    pr(f"[OBS] landing in the first window R* = 8 d_min t* in [1,7]: {pct(inwin, T)};  of which R* = 1 exactly (lap 0 of d_min): "
       f"{pct(d['R1'], T)};  R* in (1,7]: {pct(d['RMID'], T)};  R* > 7: {d['RHI']};  max R* = {frs(d['RMAX'])} at {pset(d['EXMAX'], Q)}")
    pr(f"[OBS] landing with R* in the gate (7,9): {d['RGATE']} (Gate.landing_not_in_gate [L] says none);  R* exactly 9: {d['R9']};  R* > 7 requires d_max/d_min >= {frs(d['HIMINRATIO']) if 'HIMINRATIO' in d else 'n/a (no such set)'} in this population")
    if d["EXHI"]:
        pr("      sets with R* > 7 (first six): " + "; ".join(pset(a, Q) for a in d["EXHI"]))
    byrank = defaultdict(int); bylap = defaultdict(int); tot_cls = 0
    for r, k, c, ct in d["CLASS"]: byrank[r] += c; bylap[k] += c; tot_cls += 1
    pr(f"[OBS] landing class = (rank of the smallest-rank opener, lap k) : {tot_cls} classes occur")
    pr("      by rank:", {r: byrank[r] for r in sorted(byrank)})
    pr("      by lap k:", {k: bylap[k] for k in sorted(bylap)})
    top = sorted(d["CLASS"], key=lambda z: -z[2])[:12]
    pr("      top classes (rank, lap): sets / of which tie-or-touch: " + "; ".join(f"({r},{k}): {c} / {ct}" for r, k, c, ct in top))
    pr(f"[OBS] rank 1 at lap > 0 (d_min itself the landing opener after lap 0): {d['RANK1_LAP_POS']} sets" +
       ("; first six: " + "; ".join(pset(a, Q) for a in d["EXR1"]) if d["EXR1"] else ""))
    pr(f"[OBS] explicit instants R = a (a odd in 1,3,5,7: every rho_e*a mod 8 in [1,7], rho_e = d_e/d_min): some a works in "
       f"{pct(d['EXPL_ANY'], T)}; first working a = 1: {d['EXPL_FIRST1']}, 3: {d['EXPL_FIRST3']}, 5: {d['EXPL_FIRST5']}, 7: {d['EXPL_FIRST7']}; "
       f"none works: {d['EXPL_NONE']} ({pct(d['EXPL_NONE'], T)})")
    pr(f"      landing R* is itself one of 1,3,5,7: {d['LAND_IS_ODD']};  R* = 1 coincides with 'a = 1 works': {d['R1'] == d['EXPL_FIRST1']}")
    pr(f"[OBS] forbidden disparity at the start (in the way at 1/(8 d_min)): {pct(d['NFORB_SETS'], T)}; landing at R = 1 iff none forbidden: "
       f"mismatches {d['LAP0_IFF_NOFORB_MISMATCH']}")
    pr(f"[OBS] AN exception 1: first setter is NOT the smallest forbidden disparity: {d['FS_NOT_SMALLEST']} of {d['NFORB_SETS']}" +
       ("; first six: " + "; ".join(pset(a, Q) for a in d["FSEX"]) if d["FSEX"] else ""))
    if "FSMINRATIO" in d: pr(f"      smallest d_max/d_min over the exception-1 sets: {frs(d['FSMINRATIO'])}")
    pr(f"[OBS] final cascade setter is one of the landing openers: failures {d['FINAL_NOT_OPEN']}")
    pr(f"[OBS] for sets with gcd of numerators 1 ({d['GCD1_SETS']} sets): violations of 8k+1 <= 4x at the landing opener (x = numerator): {d['GCD1_BOUND_VIOL']}")
    if tbl:
        pr(f"[OBS] AN exception 2 (residue rule: the residues rho_e mod 8 of the readings, as exact fractions, determine the landing class): "
           f"distinct residue patterns {d['PATTERNS']}; patterns carrying two or more landing classes: {d['CONFLICT_PATTERNS']}")
        if d["CONFEX"]:
            pr("      examples (pattern index, numerators over Q, landing n/(8x) in tau = t/Q, rank, lap):")
            for l in d["CONFEX"]: pr("        " + l)

def main():
    t0 = time.time()
    pr("real_case_v1.py  (task AO)  exact kernel + Fraction references")
    # 1. validations ------------------------------------------------------------------
    nbad = 0
    nbad += validate("integer sets, gcd 1, elements 1..14", 1, 14, 0)
    nbad += validate("Q=3, a/3 in [1,12], d_min = 1 (a_0 = 3)", 3, 12, 1, a0max=3)
    nbad += validate("Q=5, a/5 in [1,6]", 5, 6, 1)
    nbad += validate("Q=7, d_min = 1, a/7 in [1,8], every 211th", 7, 8, 1, a0max=7, stride=211)
    pr(f"[validation] total mismatches {nbad}")
    assert nbad == 0
    # E441 anchors: the same kernel on the integer population of E441/AN, N = 22, gcd 1
    anchor = parse(kernel("stats", 1, 22, 0, 26))
    pr(f"[validation] anchor (E441, AN): integer gcd-1 7-subsets of 1..22: {anchor['TOTAL']} sets (E441: 170,213); landing lap>0: "
       f"{anchor['RMID']} (E441: 61,958); max R* {frs(anchor['RMAX'])} (E441: 33/7)")
    assert anchor["TOTAL"] == 170213 and anchor["RMID"] == 61958 and anchor["RMAX"] == F(33, 7)
    # 2. populations -----------------------------------------------------------------
    pops = []
    report("BASELINE integer sets {1..22}, gcd 1 (E441 population; Q = 1)", 1, anchor, True,
           "sets: 7-subsets of {1..22} with gcd 1\n")
    pops.append(("integer N=22", 1, anchor))
    for (Q, HI, tb, label) in [(3, 12, 24, "Q = 3, a/3 in [1,12]"), (5, 12, 29, "Q = 5, a/5 in [1,12]"),
                               (7, 12, 0, "Q = 7, a/7 in [1,12]  (full; no pattern table: memory)")]:
        d = parse(kernel("stats", Q, HI, 1, tb))
        n_all = comb(Q * HI - Q + 1, 7); n_int = comb(HI, 7)
        extra = (f"sets: 7-subsets of {{a/{Q}}} within [1,{HI}] with primitive denominator {Q} "
                 f"(= C({Q*HI-Q+1},7) - C({HI},7) = {n_all - n_int}; kernel counted {d['TOTAL']}: {'ok' if n_all - n_int == d['TOTAL'] else 'MISMATCH'})\n")
        assert n_all - n_int == d["TOTAL"]
        report(label, Q, d, tb > 0, extra)
        pops.append((label, Q, d))
    # Q=7 restricted population requested by the brief for the residue test: [1,6] (stated: ratios <= 6)
    d = parse(kernel("stats", 7, 6, 1, 25))
    report("Q = 7, a/7 in [1,6]  (the restriction the brief allows for the pattern table; ratio d/d_min <= 6 < 7, so R = 1 is lonely for every set)", 7, d, True,
           f"sets: C({7*6-7+1},7) - C(6,7) = {comb(36,7)}\n")
    # extended-range slice for the residue-rule and first-setter exceptions
    d = parse(kernel("stats", 3, 16, 1, 25, a0max=4))
    report("Q = 3 slice: d_min in {1, 4/3}, all elements <= 16 (ratio up to 16)", 3, d, True,
           "sets: primitive denominator 3, a_0 in {3,4}, a_6 <= 48 (a slice, stated; not a full population)\n")
    pops.append(("Q=3 slice d_min<=4/3, <=16", 3, d))
    # 3. comparison table ------------------------------------------------------------
    pr("\n" + "=" * 110 + "\nCOMPARISON (all [OBS]; exact fractions)\n" + "=" * 110)
    for label, Q, d in pops:
        T = d["TOTAL"]
        pr(f"{label}: sets {T}; tie-or-touch {pct(d['TIES'] + d['TOUCH'] - d['BOTH'], T, 3)}; R* in [1,7] {pct(d['R1'] + d['RMID'], T, 3)}; "
           f"R*=1 {pct(d['R1'], T, 3)}; some odd a works {pct(d['EXPL_ANY'], T, 3)}; max R* {frs(d['RMAX'])}; rank-1 lap>0: {d['RANK1_LAP_POS']}; "
           f"first setter != smallest forbidden: {d['FS_NOT_SMALLEST']}")
    pr(f"\nelapsed {int(time.time() - t0)} s")
    shutil.rmtree(WORK)

if __name__ == "__main__":
    main()
