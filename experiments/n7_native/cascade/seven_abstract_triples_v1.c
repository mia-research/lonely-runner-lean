/* Exact: for each base set A (294 bits, 5 words) find unit masks i <= j <= k with A & m_i & m_j & m_k == 0.
   Masks restricted to A and sorted by popcount; a mask can miss p only if its popcount <= |A| - |p|.
   Usage: seven_abstract_triples_v1 units.txt bases.txt [blo bhi] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct { uint64_t w[5]; int pc; } M;
static int pc5(const uint64_t *a) { int s = 0; for (int i = 0; i < 5; i++) s += __builtin_popcountll(a[i]); return s; }
static int cmp(const void *a, const void *b) { return ((const M *)a)->pc - ((const M *)b)->pc; }
static M *rd(const char *fn, int *n) {
  FILE *f = fopen(fn, "r"); if (!f || fscanf(f, "%d", n) != 1) exit(1);
  M *m = malloc(sizeof(M) * *n);
  for (int i = 0; i < *n; i++) for (int w = 0; w < 5; w++) if (fscanf(f, "%llu", (unsigned long long *)&m[i].w[w]) != 1) exit(1);
  fclose(f); return m;
}
int main(int argc, char **argv) {
  int nu, nbase; M *u = rd(argv[1], &nu), *B = rd(argv[2], &nbase);
  int blo = argc > 4 ? atoi(argv[3]) : 0, bhi = argc > 4 ? atoi(argv[4]) : nbase;
  M *r = malloc(sizeof(M) * nu); long long covers = 0, pairs = 0;
  for (int b = blo; b < bhi; b++) {
    int A = pc5(B[b].w);
    for (int i = 0; i < nu; i++) { for (int w = 0; w < 5; w++) r[i].w[w] = u[i].w[w] & B[b].w[w]; r[i].pc = pc5(r[i].w); }
    qsort(r, nu, sizeof(M), cmp);
    int minpc = r[0].pc; long long bc = 0;
    for (int i = 0; i < nu; i++) for (int j = i; j < nu; j++) {
      uint64_t p[5]; for (int w = 0; w < 5; w++) p[w] = r[i].w[w] & r[j].w[w];
      int pp = pc5(p); pairs++;
      if (pp > A - minpc) continue;
      for (int k = j; k < nu && r[k].pc <= A - pp; k++) {
        uint64_t z = 0; for (int w = 0; w < 5; w++) z |= p[w] & r[k].w[w];
        if (!z) { bc++; if (covers + bc <= 5) printf("COVER base %d: %d %d %d\n", b, i, j, k); }
      }
    }
    covers += bc;
  }
  printf("bases [%d,%d): pairs %lld covers %lld\n", blo, bhi, pairs, covers);
  return 0;
}
