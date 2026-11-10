/* E832: refine the uncertified boxes of frontier_box_cert_v1 by halving every coordinate (64 children per box, children with no non-decreasing
   selection of readings dropped), re-test each child with a fixed clear R0 (exact integer test), level by level.
   Boxes: rho_i in [n_i/D, (n_i+1)/D].  usage: infile D0 G levels   (reads 6 ints per line); prints per level the number of children kept
   (sorted-feasible), certified, uncertified, and the uncertified volume as a multiple of the D0-box volume. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int G;
static int clear_for(int r, int n, int D) {
    ll t = (ll)r * n, u = (ll)r * (n + 1), base = (ll)G * D;
    if (t < base) return 0;
    ll j = (t - base) / (8 * base);
    return u <= (8 * j + 7) * base;
}
static int certified(const int *n, int D) {
    for (int r = G; r <= 7 * G; r++) {
        int good = 1;
        for (int i = 5; i >= 0; i--) if (!clear_for(r, n[i], D)) { good = 0; break; }
        if (good) return 1;
    }
    return 0;
}
static int sorted_feasible(const int *n) {      /* exists rho_1 <= ... <= rho_6 with rho_i in [n_i, n_i + 1] (same D) */
    int x = n[0];
    for (int i = 0; i < 6; i++) { if (n[i] > x) x = n[i]; if (x > n[i] + 1) return 0; }
    return 1;
}
int main(int argc, char **argv) {
    FILE *in = fopen(argv[1], "r"); int D = atoi(argv[2]); G = atoi(argv[3]); int levels = atoi(argv[4]);
    size_t cap = 1 << 20, cnt = 0; int *cur = malloc(cap * 6 * sizeof(int));
    int a[6];
    while (fscanf(in, "%d %d %d %d %d %d", a, a + 1, a + 2, a + 3, a + 4, a + 5) == 6) {
        if (cnt == cap) { cap *= 2; cur = realloc(cur, cap * 6 * sizeof(int)); }
        for (int i = 0; i < 6; i++) cur[cnt * 6 + i] = a[i]; cnt++;
    }
    printf("level D=%d: uncertified boxes %zu\n", D, cnt);
    for (int lv = 1; lv <= levels && cnt; lv++) {
        size_t ncap = 1 << 20, ncnt = 0; int *nxt = malloc(ncap * 6 * sizeof(int));
        ll kept = 0, cert = 0;
        for (size_t b = 0; b < cnt; b++) {
            for (int m = 0; m < 64; m++) {
                int c[6];
                for (int i = 0; i < 6; i++) c[i] = 2 * cur[b * 6 + i] + ((m >> i) & 1);
                if (!sorted_feasible(c)) continue;
                kept++;
                if (certified(c, 2 * D)) { cert++; continue; }
                if (ncnt == ncap) { ncap *= 2; nxt = realloc(nxt, ncap * 6 * sizeof(int)); }
                for (int i = 0; i < 6; i++) nxt[ncnt * 6 + i] = c[i]; ncnt++;
            }
        }
        D *= 2; free(cur); cur = nxt; cnt = ncnt;
        printf("level D=%d: children kept %lld, certified %lld, uncertified %zu\n", D, kept, cert, cnt);
        fflush(stdout);
    }
    return 0;
}
