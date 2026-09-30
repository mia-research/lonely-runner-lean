/* E196 (2026-09-30): as crowded_m1_cover_v3, with the instants restricted to order seven's form one binary digit
   finer: a = j + (N/16)*k, dilation j in 1..J (argument 3), rotation k/16.  Disallowed instants count as blocked.
   Based on E195b: one multiple of 8 with 2-adic valuation V, read at the modulus N = 8*2^W (W >= V).
   Every instant a/N, 0 < a < N, is allowed; the multiple's blocked instants are part of the union (at W > V it can
   block).  Clearness depends only on residues mod N and is invariant under units (derived): one odd residue is
   normalised to 1, the multiple runs over 2^V*c for every odd c mod 2^(W-V+3), the other five residues (non-multiples
   of 8) are enumerated non-decreasing.  Prints exceptional patterns (no lonely a/N) in canonical form. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define MAXW 8
static int N, V, W, NI;
static uint64_t B[2048][MAXW];
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
static int full(const uint64_t *U) {
  for (int i = 0; i < NI; i++) if (!((U[i / 64] >> (i % 64)) & 1)) return 0;
  return 1;
}
static void dfs(int pos, int start, const uint64_t *U) {
  if (pos == 6) { leaves++; if (full(U)) { exc++; emit(); } return; }
  for (int x = start; x < N; x++) {
    if (x % 8 == 0) continue;
    r[pos] = x;
    uint64_t X[MAXW];
    for (int w = 0; w < MAXW; w++) X[w] = U[w] | B[x][w];
    dfs(pos + 1, x, X);
  }
}
int main(int argc, char **argv) {
  V = atoi(argv[1]); W = atoi(argv[2]); N = 8 << W;
  NI = N - 1; int J = (argc > 3) ? atoi(argv[3]) : N; int G = N / 16;
  if (NI > 64 * MAXW) { fprintf(stderr, "too many instants\n"); return 1; }
  for (int x = 0; x < N; x++) {
    for (int w = 0; w < MAXW; w++) B[x][w] = 0;
    for (int a = 1; a < N; a++) {
      int t = (a * x) % N;
      int allowed = (a % G) >= 1 && (a % G) <= J;   /* dilation j = a mod (N/16) in 1..J, rotation k = a div (N/16) */
      if (!allowed || !(t >= N / 8 && t <= 7 * N / 8)) B[x][(a - 1) / 64] |= 1ULL << ((a - 1) % 64);
    }
  }
  r[0] = 1;
  int cmax = 8 << (W - V);            /* c odd mod 2^(W-V+3) */
  for (int c = 1; c < cmax; c += 2) {
    r[6] = (c << V) % N;
    uint64_t U[MAXW];
    for (int w = 0; w < MAXW; w++) U[w] = B[1][w] | B[r[6]][w];
    dfs(1, 1, U);
  }
  fprintf(stderr, "V %d W %d N %d instants %d; patterns %lld; exceptional (with repeats) %lld\n", V, W, N, NI, leaves, exc);
  return 0;
}
