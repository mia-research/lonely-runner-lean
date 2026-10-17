/* v4 (from v3): branching instant = the uncovered instant with fewest filtered candidates (all classes filter).
   v3: candidate filtering by the pair index (E27).  pairOf[s][c] = the 7-bit pair state s blocks in class c.
   At a node with r runners left and uncovered class sets X_c, a next runner with pair P in class c is admissible
   only if |X_c \ P| <= 2(r-1); and it must block the branching instant l.  Candidates = states blocking l whose
   pairs pass the test in the K fullest classes (bitset intersection over states).  Complete: every runner of a
   cover passes.  Then type-feasibility pruning (v2) and the per-class bound.  Usage: input.txt K [lo hi] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define W 4
static int NI, NM, NC, K; static int *cls, *s1, *col; static uint64_t (*M)[W]; static uint64_t (*CM)[W];
static unsigned char (*pairOf)[64]; static int cmem[64][8], ncm[64], ccol[64];
static int SW; static uint64_t *idx;   /* idx[(c*128 + P)*SW ...] bitset of states with pair P in class c */
static uint64_t *blkset;               /* blkset[l*SW ...] states blocking instant l */
static long long nodes[5], covers, pruned[5], cands[5];
static unsigned char cov1[128][7], cov2[128][7][7], cov3[128][7][7][7];
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
static int feasible(const int *Xs, int left) {
  for (int c = 0; c < NC; c++) if (__builtin_popcount(Xs[c]) > 2 * left) return 0;
  if (left >= 4) return 1;
  for (int t1 = 1; t1 < 7; t1++) for (int t2 = (left >= 2 ? t1 : 1); t2 < (left >= 2 ? 7 : 2); t2++)
    for (int t3 = (left >= 3 ? t2 : 1); t3 < (left >= 3 ? 7 : 2); t3++) {
      int ok = 1;
      for (int c = 0; c < NC && ok; c++) {
        int cc = ccol[c], X = Xs[c], d1 = inv7[(cc * t1) % 7];
        if (left == 1) ok = cov1[X][d1];
        else if (left == 2) ok = cov2[X][d1][inv7[(cc * t2) % 7]];
        else ok = cov3[X][d1][inv7[(cc * t2) % 7]][inv7[(cc * t3) % 7]];
      }
      if (ok) return 1;
    }
  return 0;
}
static void rec(const uint64_t *U, int depth) {
  nodes[depth]++;
  int left = 4 - depth;
  int Xs[64], order[64], bc = -1, best = -1;
  for (int c = 0; c < NC; c++) { Xs[c] = classX(U, c); int k = __builtin_popcount(Xs[c]); if (k > bc) { bc = k; best = c; } }
  if (bc == 0) { covers++; if (covers <= 5) printf("COVER at depth %d\n", depth); return; }
  if (left == 0) return;
  if (!feasible(Xs, left)) { pruned[depth]++; return; }
  uint64_t *C = malloc(sizeof(uint64_t) * SW), *T = malloc(sizeof(uint64_t) * SW), *F = malloc(sizeof(uint64_t) * SW);
  for (int w = 0; w < SW; w++) F[w] = ~0ULL;
  for (int c = 0; c < NC; c++) {
    int X = Xs[c];
    if (__builtin_popcount(X) <= 2 * (left - 1)) continue;   /* every pair admissible */
    memset(T, 0, sizeof(uint64_t) * SW);
    for (int P = 0; P < 128; P++) {
      if (__builtin_popcount(P) != 2) continue;
      if (__builtin_popcount(X & ~P) > 2 * (left - 1)) continue;
      const uint64_t *B = idx + ((size_t)c * 128 + P) * SW;
      for (int w = 0; w < SW; w++) T[w] |= B[w];
    }
    for (int w = 0; w < SW; w++) F[w] &= T[w];
  }
  int bestl = -1, bestn = 1 << 30;
  for (int i = 0; i < NI; i++) if (U[i / 64] >> (i % 64) & 1) {
    int n = 0; const uint64_t *Bl = blkset + (size_t)i * SW;
    for (int w = 0; w < SW; w++) n += __builtin_popcountll(F[w] & Bl[w]);
    if (n < bestn) { bestn = n; bestl = i; }
  }
  { const uint64_t *Bl = blkset + (size_t)bestl * SW; for (int w = 0; w < SW; w++) C[w] = F[w] & Bl[w]; }
  free(F);
  (void)order; (void)best;
  for (int w = 0; w < SW; w++) {
    uint64_t x = C[w];
    while (x) {
      int s = w * 64 + __builtin_ctzll(x); x &= x - 1;
      cands[depth]++;
      uint64_t V[W]; for (int q = 0; q < W; q++) V[q] = U[q] & M[s][q];
      rec(V, depth + 1);
    }
  }
  free(C); free(T);
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &NI, &NM, &NC) != 3) return 1;
  K = atoi(argv[2]);
  cls = malloc(sizeof(int) * NI); s1 = malloc(sizeof(int) * NI); col = malloc(sizeof(int) * NI);
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &cls[i]) != 1) return 1;
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &s1[i]) != 1) return 1;
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &col[i]) != 1) return 1;
  M = malloc(sizeof(uint64_t[W]) * NM);
  for (int i = 0; i < NM; i++) for (int w = 0; w < W; w++) if (fscanf(f, "%llu", (unsigned long long *)&M[i][w]) != 1) return 1;
  pairOf = malloc(64 * NM);
  for (int i = 0; i < NM; i++) for (int c = 0; c < NC; c++) { int v; if (fscanf(f, "%d", &v) != 1) return 1; pairOf[i][c] = v; }
  CM = calloc(NC, sizeof(uint64_t[W]));
  for (int i = 0; i < NI; i++) { CM[cls[i]][i / 64] |= 1ULL << (i % 64); cmem[cls[i]][ncm[cls[i]]++] = i; ccol[cls[i]] = col[i]; }
  build_tables();
  SW = (NM + 63) / 64;
  idx = calloc((size_t)NC * 128 * SW, sizeof(uint64_t));
  for (int s = 0; s < NM; s++) for (int c = 0; c < NC; c++) idx[((size_t)c * 128 + pairOf[s][c]) * SW + s / 64] |= 1ULL << (s % 64);
  blkset = calloc((size_t)NI * SW, sizeof(uint64_t));
  for (int l = 0; l < NI; l++) for (int s = 0; s < NM; s++) if (!(M[s][l / 64] >> (l % 64) & 1)) blkset[(size_t)l * SW + s / 64] |= 1ULL << (s % 64);
  uint64_t U[W] = {0}; for (int i = 0; i < NI; i++) U[i / 64] |= 1ULL << (i % 64);
  /* depth 0 handled by rec with a candidate range: emulate by filtering the root's candidate list */
  int lo = argc > 4 ? atoi(argv[3]) : 0, hi = argc > 4 ? atoi(argv[4]) : 1 << 30;
  /* root: runner 1 only; branch on first instant of the fullest class, all blockers */
  int best = 0; for (int c = 0; c < NC; c++) if (pc(CM[c]) > pc(CM[best])) best = c;
  int l0 = cmem[best][0], q = 0;
  for (int s = 0; s < NM; s++) if (!(M[s][l0 / 64] >> (l0 % 64) & 1)) {
    if (q >= lo && q < hi) { uint64_t V[W]; for (int w = 0; w < W; w++) V[w] = U[w] & M[s][w]; rec(V, 1); }
    q++;
  }
  printf("K=%d cand [%d,%d) of %d; nodes d1 %lld d2 %lld d3 %lld d4 %lld; expanded d1 %lld d2 %lld d3 %lld; pruned d1 %lld d2 %lld d3 %lld; covers %lld\n",
    K, lo, hi < q ? hi : q, q, nodes[1], nodes[2], nodes[3], nodes[4], cands[1], cands[2], cands[3], pruned[1], pruned[2], pruned[3], covers);
  return 0;
}
