/* Level A in {2,3,4} via -DA=.  Exhaustive, exact: five units (1, u2..u5) mod 2401, ui half-representatives (ui <= 1200, band symmetry u <-> 2401-u),
   sorted u2 <= u3 <= u4 <= u5.  Count tuples with no unit k mod 2401 putting every u k mod 2401 in [343, 2058].
   Masks over the 2058 unit k.  Usage: seven_level4_exh_v1 [i2_lo i2_hi]  (indices into the half-unit list) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#ifndef A
#define A 4
#endif
#if A == 2
#define N 49
#elif A == 3
#define N 343
#else
#define N 2401
#endif
#define NK (N / 7 * 6)
#define W ((NK + 63) / 64)
#define BLO (N / 7)
#define BHI (6 * (N / 7))
#define HALF (N / 2)
static uint64_t M[N][W];
int main(int argc, char **argv) {
  int ks[NK], nk = 0, hu[HALF], nh = 0;
  for (int k = 1; k < N; k++) if (k % 7) ks[nk++] = k;
  for (int u = 1; u <= HALF; u++) if (u % 7) hu[nh++] = u;
  for (int u = 1; u < N; u++) if (u % 7) {
    for (int b = 0; b < nk; b++) { int x = (int)((long)u * ks[b] % N); if (x >= BLO && x <= BHI) M[u][b >> 6] |= 1ULL << (b & 63); }
  }
  int lo = argc > 2 ? atoi(argv[1]) : 0, hi = argc > 2 ? atoi(argv[2]) : nh;
  long long tuples = 0, fails = 0; uint64_t a2[W], a3[W], a4[W];
  for (int i2 = lo; i2 < hi; i2++) {
    for (int w = 0; w < W; w++) a2[w] = M[1][w] & M[hu[i2]][w];
    for (int i3 = i2; i3 < nh; i3++) {
      for (int w = 0; w < W; w++) a3[w] = a2[w] & M[hu[i3]][w];
      for (int i4 = i3; i4 < nh; i4++) {
        for (int w = 0; w < W; w++) a4[w] = a3[w] & M[hu[i4]][w];
        for (int i5 = i4; i5 < nh; i5++) {
          const uint64_t *m5 = M[hu[i5]]; int ok = 0;
          for (int w = 0; w < W; w++) if (a4[w] & m5[w]) { ok = 1; break; }
          tuples++;
          if (!ok) { fails++; if (fails <= 20) printf("FAIL 1 %d %d %d %d\n", hu[i2], hu[i3], hu[i4], hu[i5]); }
        }
      }
    }
  }
  printf("range [%d,%d): tuples %lld fails %lld\n", lo, hi, tuples, fails);
  return 0;
}
