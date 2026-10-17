/* v2 of seven_class_bb_v1.c: adds pair-type feasibility pruning (E27).  In class (c, s0) a runner of type
   t = rho mod 7 blocks a pair {x, x+d} with d = (c t)^{-1} mod 7.  With r runners left, the node survives only if
   some multiset of r types makes every class's uncovered set (a subset of Z/7 by s1) coverable by r such pairs.
   Usage: seven_class_bb_v2 input.txt [lo hi] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define W 4
static int NI, NM, NC; static int *cls, *s1, *col; static uint64_t (*M)[W]; static uint64_t (*CM)[W];
static int **blk; static int *nblk; static int cmem[64][8], ncm[64], ccol[64];
static long long nodes[5], covers, pruned[5];
static unsigned char cov1[128][7], cov2[128][7][7], cov3[128][7][7][7];  /* [X][d1][d2][d3] coverable */
static int inv7[7] = {0, 1, 4, 5, 2, 3, 6};
static inline int pc(const uint64_t *a) { return __builtin_popcountll(a[0]) + __builtin_popcountll(a[1]) + __builtin_popcountll(a[2]) + __builtin_popcountll(a[3]); }
static int pairmask(int x, int d) { return (1 << x) | (1 << ((x + d) % 7)); }
static void build_tables(void) {
  for (int X = 0; X < 128; X++) for (int a = 1; a < 7; a++) {
    int ok = 0; for (int x = 0; x < 7; x++) if ((X & ~pairmask(x, a)) == 0) ok = 1;
    cov1[X][a] = ok;
    for (int b = 1; b < 7; b++) {
      int ok2 = 0;
      for (int x = 0; x < 7 && !ok2; x++) for (int y = 0; y < 7; y++) if ((X & ~(pairmask(x, a) | pairmask(y, b))) == 0) { ok2 = 1; break; }
      cov2[X][a][b] = ok2;
      for (int c = 1; c < 7; c++) {
        int ok3 = 0;
        for (int x = 0; x < 7 && !ok3; x++) for (int y = 0; y < 7 && !ok3; y++) for (int z = 0; z < 7; z++)
          if ((X & ~(pairmask(x, a) | pairmask(y, b) | pairmask(z, c))) == 0) { ok3 = 1; break; }
        cov3[X][a][b][c] = ok3;
      }
    }
  }
}
static int classX(const uint64_t *U, int c) {
  int X = 0; for (int k = 0; k < ncm[c]; k++) { int i = cmem[c][k]; if (U[i / 64] >> (i % 64) & 1) X |= 1 << s1[i]; }
  return X;
}
static int feasible(const uint64_t *U, int left) {
  int Xs[64]; for (int c = 0; c < NC; c++) { Xs[c] = classX(U, c); if (__builtin_popcount(Xs[c]) > 2 * left) return 0; }
  if (left >= 4) return 1;
  for (int t1 = 1; t1 < 7; t1++) for (int t2 = (left >= 2 ? t1 : 1); t2 < (left >= 2 ? 7 : 2); t2++)
    for (int t3 = (left >= 3 ? t2 : 1); t3 < (left >= 3 ? 7 : 2); t3++) {
      int ok = 1;
      for (int c = 0; c < NC && ok; c++) {
        int cc = ccol[c], X = Xs[c];
        int d1 = inv7[(cc * t1) % 7];
        if (left == 1) ok = cov1[X][d1];
        else if (left == 2) ok = cov2[X][d1][inv7[(cc * t2) % 7]];
        else ok = cov3[X][d1][inv7[(cc * t2) % 7]][inv7[(cc * t3) % 7]];
      }
      if (ok) return 1;
    }
  return 0;
}
static int pick(const uint64_t *U) {
  int best = -1, bc = 0;
  for (int c = 0; c < NC; c++) { uint64_t t[W]; for (int w = 0; w < W; w++) t[w] = U[w] & CM[c][w]; int k = pc(t); if (k > bc) { bc = k; best = c; } }
  if (best < 0) return -1;
  for (int w = 0; w < W; w++) { uint64_t t = U[w] & CM[best][w]; if (t) return w * 64 + __builtin_ctzll(t); }
  return -1;
}
static void rec(const uint64_t *U, int depth) {
  nodes[depth]++;
  int left = 4 - depth;
  int l = pick(U);
  if (l == -1) { covers++; if (covers <= 5) printf("COVER at depth %d\n", depth); return; }
  if (left == 0) return;
  if (!feasible(U, left)) { pruned[depth]++; return; }
  for (int q = 0; q < nblk[l]; q++) {
    int s = blk[l][q]; uint64_t V[W];
    for (int w = 0; w < W; w++) V[w] = U[w] & M[s][w];
    rec(V, depth + 1);
  }
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &NI, &NM, &NC) != 3) return 1;
  cls = malloc(sizeof(int) * NI); s1 = malloc(sizeof(int) * NI); col = malloc(sizeof(int) * NI);
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &cls[i]) != 1) return 1;
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &s1[i]) != 1) return 1;
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &col[i]) != 1) return 1;
  M = malloc(sizeof(uint64_t[W]) * NM);
  for (int i = 0; i < NM; i++) for (int w = 0; w < W; w++) if (fscanf(f, "%llu", (unsigned long long *)&M[i][w]) != 1) return 1;
  CM = calloc(NC, sizeof(uint64_t[W]));
  for (int i = 0; i < NI; i++) { CM[cls[i]][i / 64] |= 1ULL << (i % 64); cmem[cls[i]][ncm[cls[i]]++] = i; ccol[cls[i]] = col[i]; }
  build_tables();
  blk = malloc(sizeof(int *) * NI); nblk = calloc(NI, sizeof(int));
  for (int l = 0; l < NI; l++) { blk[l] = malloc(sizeof(int) * NM); for (int s = 0; s < NM; s++) if (!(M[s][l / 64] >> (l % 64) & 1)) blk[l][nblk[l]++] = s; }
  uint64_t U[W] = {0}; for (int i = 0; i < NI; i++) U[i / 64] |= 1ULL << (i % 64);
  int l0 = pick(U);
  int lo = argc > 3 ? atoi(argv[2]) : 0, hi = argc > 3 ? atoi(argv[3]) : nblk[l0];
  for (int q = lo; q < hi && q < nblk[l0]; q++) {
    int s = blk[l0][q]; uint64_t V[W]; for (int w = 0; w < W; w++) V[w] = U[w] & M[s][w];
    rec(V, 1);
  }
  printf("cand [%d,%d) of %d; nodes d1 %lld d2 %lld d3 %lld d4 %lld; pruned d1 %lld d2 %lld d3 %lld; covers %lld\n",
    lo, hi, nblk[l0], nodes[1], nodes[2], nodes[3], nodes[4], pruned[1], pruned[2], pruned[3], covers);
  return 0;
}
