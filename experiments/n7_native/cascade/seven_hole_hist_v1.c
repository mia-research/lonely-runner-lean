/* For the five-unit abstract problem: over all 4-tuples of minimal masks (with runner 1's restriction), record
   which instants occur as the ONLY uncovered instant (a 1-hole).  Any small instant set certifying the claim must
   contain one hole of every such tuple.  Output: per chunk, count of 1-hole tuples and the 210-bit OR of holes,
   plus a histogram line "H b count".  Usage: masks.txt ilo ihi */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct { uint64_t w[4]; int pc; } M;
static inline int pc4(const uint64_t *a) { return __builtin_popcountll(a[0]) + __builtin_popcountll(a[1]) + __builtin_popcountll(a[2]) + __builtin_popcountll(a[3]); }
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); int n, nb; if (fscanf(f, "%d %d", &n, &nb) != 2) return 1;
  M *m = malloc(sizeof(M) * n);
  for (int i = 0; i < n; i++) { for (int w = 0; w < 4; w++) if (fscanf(f, "%llu", (unsigned long long *)&m[i].w[w]) != 1) return 1; m[i].pc = pc4(m[i].w); }
  int minpc = m[0].pc;
  int ilo = atoi(argv[2]), ihi = atoi(argv[3]);
  long long cnt[16] = {0}; const int K = 4; long long hist[256] = {0}, ones = 0; (void)hist; (void)ones;
  for (int i = ilo; i < ihi; i++) for (int j = i; j < n; j++) {
    uint64_t p[4]; for (int w = 0; w < 4; w++) p[w] = m[i].w[w] & m[j].w[w];
    int pp = pc4(p); if (pp + minpc - nb > nb - minpc + K) continue;
    for (int k = j; k < n; k++) {
      uint64_t t[4]; for (int w = 0; w < 4; w++) t[w] = p[w] & m[k].w[w];
      int tp = pc4(t); if (tp > nb - minpc + K) continue;
      for (int l = k; l < n && m[l].pc <= nb - tp + K; l++) {
        uint64_t z[4]; int c = 0;
        for (int w = 0; w < 4; w++) { z[w] = t[w] & m[l].w[w]; c += __builtin_popcountll(z[w]); if (c > K) break; }
        if (c <= K) cnt[c]++;
      }
    }
  }
  for (int c = 0; c <= K; c++) printf("C %d %lld\n", c, cnt[c]);

  return 0;
}
