/* E194 (2026-09-30): the complete finite list at m = 1 -- residue patterns mod 64 for which no instant a/64 is lonely.

   Our order-seven proof's hard-branch instant, translated (E192, E193): lambda/64, lambda = j + 8k, i.e. every a/64 with
   8 not dividing a (56 instants).  Derived (E193): for a set with a multiple of 8 and none of 64 (m = 1), whether a/64
   is lonely depends only on the readings mod 64: reading d is clear at a/64 iff (a*d mod 64) lies in [8, 56].

   A pattern is a multiset of 7 residues mod 64 with: none = 0 (no multiple of 64), at least one multiple of 8, at least
   one odd residue (EightResidual's `odd`), and level-0 cost >= 8 (sum over residues not divisible by 8 of
   max(2, gcd(r, 8)); EightResidual's `cost`, since gcd(d, 8) = gcd(d mod 64, 8)).  Every such multiset is realised by
   distinct positive readings (add multiples of 64).

   Symmetry (derived): multiplying every residue by a unit u mod 64 maps the blocked instants of r to u^{-1} times those
   of r, so "some a/64 is lonely" is invariant.  One odd residue is normalised to 1; the other six are enumerated in
   non-decreasing order.  Each exceptional pattern is printed in canonical form (the least sorted tuple over the 32
   unit multiples), for deduplication by `sort -u`.  Output: one line per exceptional normalised pattern. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

static uint64_t B[64];
static int COST[64];
static int r[7];

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int cmpint(const void *x, const void *y) { return *(const int *)x - *(const int *)y; }

static void emit(void) {
  int best[7], cur[7];
  for (int i = 0; i < 7; i++) best[i] = 1000;
  for (int u = 1; u < 64; u += 2) {
    for (int i = 0; i < 7; i++) cur[i] = (u * r[i]) % 64;
    qsort(cur, 7, sizeof(int), cmpint);
    int less = 0;
    for (int i = 0; i < 7; i++) { if (cur[i] != best[i]) { less = cur[i] < best[i]; break; } }
    if (less) for (int i = 0; i < 7; i++) best[i] = cur[i];
  }
  printf("%d %d %d %d %d %d %d\n", best[0], best[1], best[2], best[3], best[4], best[5], best[6]);
}

static uint64_t FULL;
static long long leaves = 0, exceptional = 0;

static void dfs(int pos, int start, uint64_t U) {
  if (pos == 7) {
    leaves++;
    if (U != FULL) return;
    int mult = 0, cost = 0;
    for (int i = 0; i < 7; i++) { if (r[i] % 8 == 0) mult++; else cost += COST[r[i]]; }
    if (mult == 0 || cost < 8) return;
    exceptional++;
    emit();
    return;
  }
  for (int x = start; x < 64; x++) { r[pos] = x; dfs(pos + 1, x, U | B[x]); }
}

int main(void) {
  int idx = 0; int where[64];
  for (int a = 1; a < 64; a++) if (a % 8) where[a] = idx++;
  FULL = (idx == 64) ? ~0ULL : ((1ULL << idx) - 1);
  for (int x = 0; x < 64; x++) {
    B[x] = 0;
    for (int a = 1; a < 64; a++) if (a % 8) {
      int v = (a * x) % 64;
      if (!(v >= 8 && v <= 56)) B[x] |= 1ULL << where[a];
    }
    COST[x] = (x % 8) ? (gcd(x, 8) > 2 ? gcd(x, 8) : 2) : 0;
  }
  r[0] = 1;
  dfs(1, 1, B[1]);
  fprintf(stderr, "instants %d; normalised patterns enumerated %lld; exceptional (with repeats across orbits) %lld\n",
          idx, leaves, exceptional);
  return 0;
}
