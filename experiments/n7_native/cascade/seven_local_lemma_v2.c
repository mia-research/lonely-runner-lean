/* Local digit lemma, exhaustive DFS (EXACT integers).  Runner state (u0,u1,e,D), u0 in 1..6, others 0..6.
   Row y (0..6), column s (0..6): top digit (D + u1*y + (e+u0*y)/7 + u0*s) % 7; FORBIDDEN iff in {0,6}.
   Each state forbids exactly two columns per row.  Search all multisets of 5 states whose forbidden sets cover every
   (y,s) (i.e. leave no allowed cell).  Prune: after j states, each row's uncovered count must be <= 2*(5-j).
   Prints the number of covering 5-multisets and the first few. */
#include <stdio.h>
#include <stdint.h>
typedef unsigned long long u64;
static u64 F[2058]; static int st[2058][4]; static int NS = 0;
static long long found = 0;
static int pc7(u64 x, int y) { return __builtin_popcountll((x >> (7*y)) & 127ULL); }
static int ok(u64 cov, int left) {      /* uncovered per row <= 2*left */
    for (int y = 0; y < 7; y++) if (7 - pc7(cov, y) > 2*left) return 0;
    return 1;
}
static int pick[5];
static void dfs(int j, int start, u64 cov) {
    if (j == 5) {
        if (cov == ((1ULL << 49) - 1)) {
            if (found < 5) {
                printf("covering:");
                for (int i = 0; i < 5; i++) printf(" (%d,%d,%d,%d)", st[pick[i]][0], st[pick[i]][1], st[pick[i]][2], st[pick[i]][3]);
                printf("\n");
            }
            found++;
        }
        return;
    }
    for (int i = start; i < NS; i++) {
        u64 c = cov | F[i];
        if (!ok(c, 4 - j)) continue;
        pick[j] = i; dfs(j + 1, i, c);
    }
}
int main(void) {
    for (int u0 = 1; u0 <= 6; u0++) for (int u1 = 0; u1 < 7; u1++) for (int e = 0; e < 7; e++) for (int D = 0; D < 7; D++) {
        u64 m = 0;
        for (int y = 0; y < 7; y++) for (int s = 0; s < 7; s++) {
            int t = (D + u1*y + (e + u0*y)/7 + u0*s) % 7;
            if (t == 0 || t == 6) m |= 1ULL << (7*y + s);
        }
        F[NS] = m; st[NS][0] = u0; st[NS][1] = u1; st[NS][2] = e; st[NS][3] = D; NS++;
    }
    dfs(0, 0, 0ULL);
    printf("states %d, covering 5-multisets: %lld\n", NS, found);
    return 0;
}
