/* Class-ordered branch-and-bound for the five-unit abstract claim (E27 route; order 8's "branch on the lowest
   uncovered residue", here: on an uncovered instant of the fullest class).  Exact.
   U = instants still good for every chosen runner (runner 1 fixed).  A cover needs U empty after four runners.
   Branch: pick the class with most members in U, an instant l in it; the next runner must block l (complete).
   Prune: with r runners left, every class must have at most 2r members in U (each runner blocks exactly 2 of the
   7 members of every class).  Depth-0 candidates may be split across processes.
   Usage: seven_class_bb_v1 input.txt [lo hi]   (lo, hi index the depth-0 candidate list) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#define W 4
static int NI, NM, NC; static int *cls; static uint64_t (*M)[W]; static uint64_t (*CM)[W];
static int **blk; static int *nblk;   /* blk[l] = states blocking instant l */
static long long nodes[5], covers;
static inline int pc(const uint64_t *a) { return __builtin_popcountll(a[0]) + __builtin_popcountll(a[1]) + __builtin_popcountll(a[2]) + __builtin_popcountll(a[3]); }
static int pick(const uint64_t *U, int left) {   /* returns instant, or -2 if pruned, -1 if U empty */
  int best = -1, bc = 0;
  for (int c = 0; c < NC; c++) {
    uint64_t t[W]; for (int w = 0; w < W; w++) t[w] = U[w] & CM[c][w];
    int k = pc(t);
    if (k > 2 * left) return -2;
    if (k > bc) { bc = k; best = c; }
  }
  if (best < 0) return -1;
  for (int w = 0; w < W; w++) { uint64_t t = U[w] & CM[best][w]; if (t) return w * 64 + __builtin_ctzll(t); }
  return -1;
}
static void rec(const uint64_t *U, int depth) {
  nodes[depth]++;
  int left = 4 - depth;
  int l = pick(U, left);
  if (l == -1) { covers++; if (covers <= 5) printf("COVER at depth %d\n", depth); return; }
  if (l == -2 || left == 0) return;
  for (int q = 0; q < nblk[l]; q++) {
    int s = blk[l][q]; uint64_t V[W];
    for (int w = 0; w < W; w++) V[w] = U[w] & M[s][w];
    rec(V, depth + 1);
  }
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &NI, &NM, &NC) != 3) return 1;
  cls = malloc(sizeof(int) * NI); for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &cls[i]) != 1) return 1;
  M = malloc(sizeof(uint64_t[W]) * NM);
  for (int i = 0; i < NM; i++) for (int w = 0; w < W; w++) if (fscanf(f, "%llu", (unsigned long long *)&M[i][w]) != 1) return 1;
  CM = calloc(NC, sizeof(uint64_t[W]));
  for (int i = 0; i < NI; i++) CM[cls[i]][i / 64] |= 1ULL << (i % 64);
  blk = malloc(sizeof(int *) * NI); nblk = calloc(NI, sizeof(int));
  for (int l = 0; l < NI; l++) { blk[l] = malloc(sizeof(int) * NM); for (int s = 0; s < NM; s++) if (!(M[s][l / 64] >> (l % 64) & 1)) blk[l][nblk[l]++] = s; }
  uint64_t U[W] = {0}; for (int i = 0; i < NI; i++) U[i / 64] |= 1ULL << (i % 64);
  int l0 = pick(U, 4);
  int lo = argc > 3 ? atoi(argv[2]) : 0, hi = argc > 3 ? atoi(argv[3]) : nblk[l0];
  nodes[0] = 1;
  for (int q = lo; q < hi && q < nblk[l0]; q++) {
    int s = blk[l0][q]; uint64_t V[W]; for (int w = 0; w < W; w++) V[w] = U[w] & M[s][w];
    rec(V, 1);
  }
  printf("depth-0 candidates [%d,%d) of %d; nodes d1 %lld d2 %lld d3 %lld d4 %lld; covers %lld\n", lo, hi, nblk[l0], nodes[1], nodes[2], nodes[3], nodes[4], covers);
  return 0;
}
