/* E195 (2026-09-30): the exhaustive list at the 2-adic top modulus, one multiple of 8.
   E194: the top level's cofactor must be a unit; take N = 8*2^v, v the 2-adic valuation of the multiple of 8.
   Here: exactly one multiple of 8, with 2-adic valuation v (argument; v = 4 gives N = 128), six non-multiples of 8.
   Instants a/N with 8 not dividing a: the multiple 2^v*c (c odd) reads c*a/8, clear iff 8 does not divide a.
   A reading d is clear at a/N iff (a*d mod N) lies in [N/8, 7N/8].  Clearness depends only on residues mod N and is
   invariant under multiplying all residues by a unit (derived), so one odd residue is normalised to 1 and the multiple
   runs over 2^v * c for every odd c; each exceptional
   pattern is printed in canonical form (least sorted tuple over all units) for `sort -u`.
   Level-0 cost is 12 or more automatically (six non-multiples at cost >= 2).  Needs one odd reading: 1 is present. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define MAXW 4
static int N, V, NI;
static uint64_t B[1024][MAXW];
static int r[7];
static long long leaves = 0, exc = 0;
static int cmpint(const void *x, const void *y) { return *(const int *)x - *(const int *)y; }
static void emit(void) {
  int best[7], cur[7];
  for (int i = 0; i < 7; i++) best[i] = 1 << 30;
  for (int u = 1; u < N; u += 2) {
    for (int i = 0; i < 7; i++) cur[i] = (u * r[i]) % N;
    qsort(cur, 7, sizeof(int), cmpint);
    for (int i = 0; i < 7; i++) { if (cur[i] != best[i]) { if (cur[i] < best[i]) for (int k = 0; k < 7; k++) best[k] = cur[k]; break; } }
  }
  for (int i = 0; i < 7; i++) printf("%d%c", best[i], i < 6 ? ' ' : '\n');
}
static void dfs(int pos, int start, uint64_t *U) {
  if (pos == 6) {
    leaves++;
    uint64_t W[MAXW];
    for (int w = 0; w < MAXW; w++) W[w] = U[w] | B[r[6]][w];
    int full = 1;
    for (int i = 0; i < NI; i++) if (!((W[i / 64] >> (i % 64)) & 1)) { full = 0; break; }
    if (full) { exc++; emit(); }
    return;
  }
  for (int x = start; x < N; x++) {
    if (x % 8 == 0) continue;
    r[pos] = x;
    uint64_t W[MAXW];
    for (int w = 0; w < MAXW; w++) W[w] = U[w] | B[x][w];
    dfs(pos + 1, x, W);
  }
}
int main(int argc, char **argv) {
  V = atoi(argv[1]); N = 8 << V;
  int idx = 0, where[1024];
  for (int a = 1; a < N; a++) if (a % 8) where[a] = idx++;
  NI = idx;
  if (NI > 64 * MAXW) { fprintf(stderr, "too many instants\n"); return 1; }
  for (int x = 0; x < N; x++) {
    for (int w = 0; w < MAXW; w++) B[x][w] = 0;
    for (int a = 1; a < N; a++) if (a % 8) {
      int t = (a * x) % N;
      if (!(t >= N / 8 && t <= 7 * N / 8)) B[x][where[a] / 64] |= 1ULL << (where[a] % 64);
    }
  }
  /* After an odd residue is normalised to 1 no unit freedom is left, so the multiple 2^v*c runs over every odd c
     mod 8 (its residues mod N are 2^v times the odd residues mod 2^(3)): corrected 2026-09-30 before any use of the
     first run, which fixed c = 1 only. */
  r[0] = 1;
  for (int c = 1; c < 8; c += 2) {
    r[6] = (c << V) % N;
    uint64_t U[MAXW];
    for (int w = 0; w < MAXW; w++) U[w] = B[1][w];
    dfs(1, 1, U);
  }
  fprintf(stderr, "v %d N %d instants %d; patterns %lld; exceptional (with repeats) %lld\n", V, N, NI, leaves, exc);
  return 0;
}
