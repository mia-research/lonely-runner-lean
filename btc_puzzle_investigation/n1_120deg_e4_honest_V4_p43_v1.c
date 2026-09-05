#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define P 43
#define N 31   /* #E(F_p) */
#define B 7
typedef long long ll;

/* ---- field parameterized by m and reduction poly fp[m] (f = x^m + sum fp[j] x^j) ---- */
static int M, FP[4];
static ll Q; /* p^m */
static ll PW[5]; /* p^j */

static inline void decode(ll e,int*c){ for(int j=0;j<M;j++){ c[j]=(int)((e/PW[j])%P);} }
static inline ll encode(const int*c){ ll e=0; for(int j=0;j<M;j++) e+=(ll)c[j]*PW[j]; return e; }

static void fmul(const int*A,const int*B_,int*out){
    long acc[8]; for(int i=0;i<2*M-1;i++) acc[i]=0;
    for(int i=0;i<M;i++) if(A[i]) for(int j=0;j<M;j++) acc[i+j]+=(long)A[i]*B_[j];
    for(int i=0;i<2*M-1;i++) acc[i]%=P;
    for(int d=2*M-2; d>=M; d--){ long c=acc[d]%P; if(c){ for(int j=0;j<M;j++){ acc[d-M+j]=(acc[d-M+j]-c*FP[j])%P; } } acc[d]=0; }
    for(int i=0;i<M;i++){ int v=(int)(acc[i]%P); if(v<0)v+=P; out[i]=v; }
}
static void fpow(const int*A,ll e,int*out){
    int R[4]={0},Bb[4]; R[0]=1; for(int i=0;i<M;i++)Bb[i]=A[i];
    while(e){ if(e&1){int t[4]; fmul(R,Bb,t); memcpy(R,t,sizeof(int)*M);} int t2[4]; fmul(Bb,Bb,t2); memcpy(Bb,t2,sizeof(int)*M); e>>=1; }
    memcpy(out,R,sizeof(int)*M);
}
static void finv(const int*A,int*out){ fpow(A,Q-2,out); }
static int fzero(const int*A){ for(int i=0;i<M;i++) if(A[i])return 0; return 1; }
static int feq(const int*A,const int*B_){ for(int i=0;i<M;i++) if(A[i]!=B_[i])return 0; return 1; }

/* EC over F_{p^m}: point = (x[4],y[4],inf) */
typedef struct{int x[4],y[4],inf;} Pt;
static void ecadd(const Pt*Pp,const Pt*Qp,Pt*R){
    if(Pp->inf){*R=*Qp;return;} if(Qp->inf){*R=*Pp;return;}
    int negy[4]; for(int i=0;i<M;i++){int v=(-Qp->y[i])%P; if(v<0)v+=P; negy[i]=v;}
    if(feq(Pp->x,Qp->x)){
        if(feq(Pp->y,negy)){ R->inf=1; return; }
    }
    int num[4],den[4];
    if(feq(Pp->x,Qp->x)&&feq(Pp->y,Qp->y)){
        int three[4]={0},x2[4]; three[0]=3; fmul(Pp->x,Pp->x,x2); fmul(three,x2,num);
        int two[4]={0}; two[0]=2; fmul(two,Pp->y,den);
    } else {
        for(int i=0;i<M;i++){int v=(Qp->y[i]-Pp->y[i])%P; if(v<0)v+=P; num[i]=v;}
        for(int i=0;i<M;i++){int v=(Qp->x[i]-Pp->x[i])%P; if(v<0)v+=P; den[i]=v;}
    }
    int di[4],m_[4]; finv(den,di); fmul(num,di,m_);
    int m2[4]; fmul(m_,m_,m2);
    int x3[4]; for(int i=0;i<M;i++){int v=(m2[i]-Pp->x[i]-Qp->x[i])%P; if(v<0)v+=P; x3[i]=v;}
    int dx[4]; for(int i=0;i<M;i++){int v=(Pp->x[i]-x3[i])%P; if(v<0)v+=P; dx[i]=v;}
    int y3[4]; fmul(m_,dx,y3); for(int i=0;i<M;i++){int v=(y3[i]-Pp->y[i])%P; if(v<0)v+=P; y3[i]=v;}
    R->inf=0; memcpy(R->x,x3,sizeof(int)*M); memcpy(R->y,y3,sizeof(int)*M);
}

/* base field idx */
static int idxb[P][P];
static int legendre(int a){ a%=P; if(a<0)a+=P; if(a==0)return 0; int r=1,base=a,e=(P-1)/2; while(e){if(e&1)r=(int)((ll)r*base%P); base=(int)((ll)base*base%P); e>>=1;} return r==1?1:-1; }

static void setfield(int m){
    M=m; Q=1; for(int i=0;i<m;i++)Q*=P;
    PW[0]=1; for(int j=1;j<=4;j++)PW[j]=PW[j-1]*P;
    if(m==2){FP[0]=1;FP[1]=0;}
    else if(m==3){FP[0]=1;FP[1]=0;FP[2]=9;}
    else if(m==4){FP[0]=1;FP[1]=0;FP[2]=0;FP[3]=5;}
}

/* compute V_m(a) for a=1,2 into vec[2][N]; m>=2 uses tables */
static void computeVm(int m, ll vec[2][N]){
    setfield(m);
    ll q=Q;
    char*is_sq=calloc(q,1);
    ll*sqrt_tab=malloc(sizeof(ll)*q);
    ll*frob=malloc(sizeof(ll)*q);
    for(ll e=0;e<q;e++){ int c[4]; decode(e,c); int s[4]; fmul(c,c,s); ll es=encode(s); is_sq[es]=1; sqrt_tab[es]=e; int fc[4]; fpow(c,P,fc); frob[e]=encode(fc); }
    for(int a=0;a<2;a++) for(int i=0;i<N;i++) vec[a][i]=0;
    int be[4]; /* b embedded */
    for(ll xe=0; xe<q; xe++){
        int x[4]; decode(xe,x);
        int x2[4],x3[4]; fmul(x,x,x2); fmul(x2,x,x3);
        int rhs[4]; memcpy(rhs,x3,sizeof(int)*M); rhs[0]=(rhs[0]+B)%P;
        if(fzero(rhs)) continue;
        ll er=encode(rhs); if(!is_sq[er]) continue;
        ll ye=sqrt_tab[er];
        for(int sgn=0;sgn<2;sgn++){
            ll yy = ye;
            if(sgn){ int yc[4]; decode(ye,yc); for(int i=0;i<M;i++){int v=(-yc[i])%P; if(v<0)v+=P; yc[i]=v;} yy=encode(yc); }
            int chi2 = is_sq[yy] ? 1 : -1; /* y!=0 */
            /* Norm = Q + Frob Q + Frob^2 Q + Frob^3 Q */
            Pt S; S.inf=0; int xc[4],yc2[4]; decode(xe,xc); decode(yy,yc2); memcpy(S.x,xc,sizeof(int)*M); memcpy(S.y,yc2,sizeof(int)*M);
            ll fx=xe, fy=yy;
            for(int i=1;i<M;i++){
                fx=frob[fx]; fy=frob[fy];
                Pt F; F.inf=0; decode(fx,F.x); decode(fy,F.y);
                Pt T; ecadd(&S,&F,&T); S=T;
            }
            int k;
            if(S.inf) k=0;
            else {
                /* S must be base field: coords[1..]==0 */
                k=idxb[S.x[0]][S.y[0]];
            }
            for(int a=0;a<2;a++){ int aa=(a+1); vec[a][(aa*k)%N]-=chi2; }
        }
    }
    free(is_sq);free(sqrt_tab);free(frob);
}

/* base V1 via cycle */
static int Gx,Gy;
static void ec_add_Fp(int x1,int y1,int i1,int x2,int y2,int i2,int*rx,int*ry,int*ri){
    if(i1){*rx=x2;*ry=y2;*ri=i2;return;} if(i2){*rx=x1;*ry=y1;*ri=i1;return;}
    if(x1==x2 && (y1+y2)%P==0){*ri=1;return;}
    ll m;
    if(x1==x2&&y1==y2){ ll inv=1,bs=(2*y1)%P,e=P-2; while(e){if(e&1)inv=inv*bs%P; bs=bs*bs%P; e>>=1;} m=((ll)3*x1%P*x1%P)*inv%P; }
    else { ll inv=1,bs=((x2-x1)%P+P)%P,e=P-2; while(e){if(e&1)inv=inv*bs%P; bs=bs*bs%P; e>>=1;} m=(((y2-y1)%P+P)%P)*inv%P; }
    ll x3=((m*m - x1 - x2)%P+P)%P; ll y3=((m*(x1-x3))%P - y1); y3=((y3%P)+P)%P;
    *rx=(int)x3;*ry=(int)y3;*ri=0;
}
int main(){
    /* base E(F_p): points x-major y-major */
    setfield(1); for(int i=0;i<=4;i++)PW[i]=1; PW[0]=1;PW[1]=P;PW[2]=P*P;PW[3]=P*P*P;PW[4]=(ll)P*P*P*P;
    for(int i=0;i<P;i++)for(int j=0;j<P;j++)idxb[i][j]=-1;
    int firstx=-1,firsty=-1;
    for(int x=0;x<P&&firstx<0;x++){int rhs=((x*x%P)*x+B)%P; for(int y=0;y<P;y++){ if((y*y-rhs)%P==0){ firstx=x;firsty=y; break;} }}
    Gx=firstx;Gy=firsty;
    /* cycle */
    int cx=Gx,cy=Gy,ci=0; int k=1; idxb[cx][cy]=1;
    int Vcyc_y[N];
    Vcyc_y[1]=cy;
    for(k=2;k<N;k++){ int nx,ny,ni; ec_add_Fp(cx,cy,ci,Gx,Gy,0,&nx,&ny,&ni); cx=nx;cy=ny;ci=ni; idxb[cx][cy]=k; Vcyc_y[k]=cy; }
    /* V1(a) a=1,2 */
    ll v1[2][N]; for(int a=0;a<2;a++)for(int i=0;i<N;i++)v1[a][i]=0;
    for(int kk=1;kk<N;kk++){ int c=legendre(Vcyc_y[kk]); if(c) for(int a=0;a<2;a++){int aa=a+1; v1[a][(aa*kk)%N]-=c;} }
    ll v2[2][N],v3[2][N],v4[2][N];
    computeVm(2,v2); computeVm(3,v3); computeVm(4,v4);
    for(int a=0;a<2;a++){
        printf("V1_%d",a+1); for(int i=0;i<N;i++)printf(" %lld",v1[a][i]); printf("\n");
        printf("V2_%d",a+1); for(int i=0;i<N;i++)printf(" %lld",v2[a][i]); printf("\n");
        printf("V3_%d",a+1); for(int i=0;i<N;i++)printf(" %lld",v3[a][i]); printf("\n");
        printf("V4_%d",a+1); for(int i=0;i<N;i++)printf(" %lld",v4[a][i]); printf("\n");
    }
    return 0;
}
