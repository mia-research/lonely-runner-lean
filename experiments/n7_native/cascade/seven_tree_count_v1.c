/* Count nodes of the pruned search tree for the five-unit abstract claim.
   Masks over runner 1's 210 instants, grouped by c (35 per c).  Each runner forbids at most 14 per c, so a partial
   set with r runners left must leave at most 14 r uncovered in every c-block.  Input: masks file with c-block
   layout produced by seven_tree_prep_v1.py (6 blocks x 64-bit word, 35 bits used each). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); int n; if (fscanf(f, "%d", &n) != 1) return 1;
  uint64_t (*m)[6] = malloc(sizeof(uint64_t[6]) * n);
  for (int i = 0; i < n; i++) for (int c = 0; c < 6; c++) if (fscanf(f, "%llu", (unsigned long long *)&m[i][c]) != 1) return 1;
  long long p2 = 0, p3 = 0, covers = 0;
  int ilo = argc > 3 ? atoi(argv[2]) : 0, ihi = argc > 3 ? atoi(argv[3]) : n;
  for (int i = ilo; i < ihi; i++) for (int j = i; j < n; j++) {
    uint64_t a[6]; int ok = 1;
    for (int c = 0; c < 6; c++) { a[c] = m[i][c] & m[j][c]; if (__builtin_popcountll(a[c]) > 28) { ok = 0; break; } }
    if (!ok) continue; p2++;
    for (int k = j; k < n; k++) {
      uint64_t b[6]; int ok3 = 1;
      for (int c = 0; c < 6; c++) { b[c] = a[c] & m[k][c]; if (__builtin_popcountll(b[c]) > 14) { ok3 = 0; break; } }
      if (!ok3) continue; p3++;
      for (int l = k; l < n; l++) { int z = 1; for (int c = 0; c < 6; c++) if (b[c] & m[l][c]) { z = 0; break; } if (z) covers++; }
    }
  }
  printf("i [%d,%d): pairs surviving %lld, triples surviving %lld, covers %lld\n", ilo, ihi, p2, p3, covers);
  return 0;
}
