/* Exact: given n masks over nb <= 256 bits (4 words), find i<=j<=k<=l with m_i & m_j & m_k & m_l == 0.
   Pruning: a mask of popcount P can be disjoint from t only if P <= nb - popcount(t); masks sorted by popcount.
   Usage: seven_abstract_cover_v1 masks.txt [ilo ihi] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct { uint64_t w[4]; int pc; } M;
static M *m; static int n, nb;
static inline int pc4(const uint64_t *a) { return __builtin_popcountll(a[0]) + __builtin_popcountll(a[1]) + __builtin_popcountll(a[2]) + __builtin_popcountll(a[3]); }
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d", &n, &nb) != 2) return 1;
  m = malloc(sizeof(M) * n);
  for (int i = 0; i < n; i++) { for (int w = 0; w < 4; w++) if (fscanf(f, "%llu", (unsigned long long *)&m[i].w[w]) != 1) return 1; m[i].pc = pc4(m[i].w); }
  int minpc = m[0].pc; for (int i = 1; i < n; i++) if (m[i].pc < minpc) minpc = m[i].pc;
  int ilo = argc > 3 ? atoi(argv[2]) : 0, ihi = argc > 3 ? atoi(argv[3]) : n;
  long long triples = 0, survivors = 0, covers = 0;
  for (int i = ilo; i < ihi; i++) for (int j = i; j < n; j++) {
    uint64_t p[4]; for (int w = 0; w < 4; w++) p[w] = m[i].w[w] & m[j].w[w];
    int pp = pc4(p); if (pp + minpc - nb > nb - minpc) continue; /* |p & m_k| >= pp + minpc - nb must be <= nb - minpc */
    for (int k = j; k < n; k++) {
      uint64_t t[4]; for (int w = 0; w < 4; w++) t[w] = p[w] & m[k].w[w];
      int tp = pc4(t); triples++;
      if (tp > nb - minpc) continue;
      survivors++;
      for (int l = k; l < n && m[l].pc <= nb - tp; l++) {
        if (!((t[0] & m[l].w[0]) | (t[1] & m[l].w[1]) | (t[2] & m[l].w[2]) | (t[3] & m[l].w[3]))) {
          covers++; if (covers <= 10) printf("COVER %d %d %d %d\n", i, j, k, l);
        }
      }
    }
  }
  printf("i in [%d,%d): triples %lld, popcount survivors %lld, covers %lld\n", ilo, ihi, triples, survivors, covers);
  return 0;
}
