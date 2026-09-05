/* Full 2^32 seed sweep for CPython's random.Random (Mersenne Twister), in C.
 * Faithful port of CPython Modules/_randommodule.c: init_by_array seeding,
 * genrand_uint32 tempering, getrandbits, and randrange/_randbelow. Three
 * consumption models for building puzzle key #N (N bits, top bit set):
 *   model 0 = randrange(2^(N-1), 2^N)   [_randbelow, getrandbits(N)+reject]
 *   model 1 = topbit: (1<<(N-1)) | getrandbits(N-1)
 *   model 2 = reject: getrandbits(N) until >= 2^(N-1)
 * Usage:
 *   ./mt_sweep sweep MODEL LO HI      -> prints "best_run best_seed" over [LO,HI)
 *   ./mt_sweep dump  MODEL SEED NPRINT-> prints first NPRINT keys (validation)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define N 624
#define M 397
#define MATRIX_A 0x9908b0dfUL
#define UPPER 0x80000000UL
#define LOWER 0x7fffffffUL
#include "keys.h"
typedef unsigned int u32;
typedef unsigned long long u64;
typedef unsigned __int128 u128;

typedef struct { u32 mt[N]; int mti; } MT;

static void init_genrand(MT *st, u32 s){
    st->mt[0]=s & 0xffffffffUL;
    for(int i=1;i<N;i++) st->mt[i]=(1812433253UL*(st->mt[i-1]^(st->mt[i-1]>>30))+i)&0xffffffffUL;
    st->mti=N;
}
static void init_by_array(MT *st,const u32*key,int klen){
    init_genrand(st,19650218UL);
    int i=1,j=0; int k=(N>klen?N:klen);
    for(;k;k--){
        st->mt[i]=((st->mt[i]^((st->mt[i-1]^(st->mt[i-1]>>30))*1664525UL))+key[j]+j)&0xffffffffUL;
        i++;j++; if(i>=N){st->mt[0]=st->mt[N-1];i=1;} if(j>=klen)j=0;
    }
    for(k=N-1;k;k--){
        st->mt[i]=((st->mt[i]^((st->mt[i-1]^(st->mt[i-1]>>30))*1566083941UL))-i)&0xffffffffUL;
        i++; if(i>=N){st->mt[0]=st->mt[N-1];i=1;}
    }
    st->mt[0]=0x80000000UL;
}
static inline u32 genrand(MT *st){
    u32 y; static const u32 mag01[2]={0,MATRIX_A};
    if(st->mti>=N){
        int kk;
        for(kk=0;kk<N-M;kk++){y=(st->mt[kk]&UPPER)|(st->mt[kk+1]&LOWER);st->mt[kk]=st->mt[kk+M]^(y>>1)^mag01[y&1];}
        for(;kk<N-1;kk++){y=(st->mt[kk]&UPPER)|(st->mt[kk+1]&LOWER);st->mt[kk]=st->mt[kk+(M-N)]^(y>>1)^mag01[y&1];}
        y=(st->mt[N-1]&UPPER)|(st->mt[0]&LOWER);st->mt[N-1]=st->mt[M-1]^(y>>1)^mag01[y&1];
        st->mti=0;
    }
    y=st->mt[st->mti++];
    y^=y>>11; y^=(y<<7)&0x9d2c5680UL; y^=(y<<15)&0xefc60000UL; y^=y>>18;
    return y;
}
/* getrandbits(k), k up to ~96, CPython little-endian word assembly */
static inline u128 getrandbits(MT *st,int k){
    if(k<=32) return (u128)(genrand(st)>>(32-k));
    u128 res=0; int shift=0;
    while(k>0){
        u32 r=genrand(st);
        if(k<32) r>>=(32-k);
        res |= (u128)r<<shift;
        shift+=32; k-=32;
    }
    return res;
}
static inline void seed_int(MT*st,u32 s){ u32 key[1]={s}; init_by_array(st,key,1); }

/* build key #idx (0-based, N=idx+1 bits) under model; returns 128-bit value */
static inline u128 make_key(MT*st,int idx,int model){
    int Nb=idx+1;                 /* bit length */
    u128 top=(u128)1<<(idx);      /* 2^(Nb-1) */
    if(model==1){                 /* topbit */
        return top | (Nb>1?getrandbits(st,Nb-1):0);
    } else if(model==2){          /* reject: getrandbits(Nb) until >=top */
        u128 r;
        do{ r=getrandbits(st,Nb); }while(r<top);
        return r;
    } else {                      /* randrange(top,2^Nb): _randbelow(top), k=Nb */
        u128 r;
        do{ r=getrandbits(st,Nb); }while(r>=top);  /* width=top=2^(Nb-1), bit_length=Nb */
        return top + r;
    }
}
static inline u128 target(int i){ return ((u128)KEY_HI[i]<<64)|KEY_LO[i]; }

int main(int argc,char**argv){
    if(argc<3){fprintf(stderr,"usage\n");return 1;}
    int model=atoi(argv[2]);
    if(!strcmp(argv[1],"dump")){
        u32 seed=(u32)strtoull(argv[3],0,10); int np=atoi(argv[4]);
        MT st; seed_int(&st,seed);
        for(int i=0;i<np;i++){ u128 k=make_key(&st,i,model);
            printf("%llu %llu\n",(u64)(k>>64),(u64)k); }
        return 0;
    }
    if(!strcmp(argv[1],"sweep")){
        u64 lo=strtoull(argv[3],0,10), hi=strtoull(argv[4],0,10);
        int best=0; u64 bestseed=0;
        for(u64 s=lo;s<hi;s++){
            MT st; seed_int(&st,(u32)s);
            int run=0;
            for(int i=0;i<NKEYS;i++){
                if(make_key(&st,i,model)==target(i)) run++; else break;
            }
            if(run>best){best=run;bestseed=s; if(run>=NKEYS)break;}
        }
        printf("%d %llu\n",best,bestseed);
        return 0;
    }
    return 1;
}
