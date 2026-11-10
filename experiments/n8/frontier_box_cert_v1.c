/* E832: exact box certificates that no carve of [1,7] exists.  A box is  rho_i in [n_i/D, (n_i+1)/D]  (i = 2..7, n_2 <= ... <= n_7, n_i >= D).
   A rational R0 = r/G in [1,7] is CLEAR for the whole box when, for every reading i, R0 * [n_i/D, (n_i+1)/D] lies inside one closed clear gap
   [8j+1, 8j+7] of the zone pattern (so rho R0 is at distance >= 1 from every multiple of 8 for every rho in the box).  Reading 1 is clear on all of [1,7].
   Then every arrangement in the box has a lonely instant R0 in W_0: the box holds no carve.  Integer arithmetic only.
   usage: D G lo7 hi7  (top reading's lower corner n7 in [lo7*D, hi7*D - 1]); prints counts and writes uncertified boxes to the file given as argv[5] if present. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int D, G;
static int clear_for(int r, int n) {          /* reading box [n, n+1]/D with R0 = r/G */
    ll t = (ll)r * n;                          /* R0 * lower end = t / (G D) */
    ll u = (ll)r * (n + 1);
    ll base = (ll)G * D;
    if (t < base) return 0;                    /* R0 * rho < 1: not possible for rho >= 1, R0 >= 1 */
    ll j = (t - base) / (8 * base);            /* largest j with 8j+1 <= t/base */
    return u <= (8 * j + 7) * base;
}
int main(int argc, char **argv) {
    D = atoi(argv[1]); G = atoi(argv[2]); int lo7 = atoi(argv[3]), hi7 = atoi(argv[4]);
    FILE *out = argc > 5 ? fopen(argv[5], "w") : NULL;
    ll total = 0, cert = 0, unc = 0;
    int n[6];
    int nmin = D;
    for (n[5] = lo7 * D; n[5] < hi7 * D; n[5]++)
    for (n[4] = nmin; n[4] <= n[5]; n[4]++)
    for (n[3] = nmin; n[3] <= n[4]; n[3]++)
    for (n[2] = nmin; n[2] <= n[3]; n[2]++)
    for (n[1] = nmin; n[1] <= n[2]; n[1]++)
    for (n[0] = nmin; n[0] <= n[1]; n[0]++) {
        total++;
        int ok = 0;
        for (int r = G; r <= 7 * G && !ok; r++) {
            int good = 1;
            for (int i = 5; i >= 0; i--) if (!clear_for(r, n[i])) { good = 0; break; }
            if (good) ok = 1;
        }
        if (ok) cert++; else { unc++; if (out) fprintf(out, "%d %d %d %d %d %d\n", n[0], n[1], n[2], n[3], n[4], n[5]); }
    }
    printf("D=%d G=%d top reading lower corner in [%d,%d): boxes %lld, certified (a fixed clear R0 exists) %lld, uncertified %lld\n", D, G, lo7, hi7, total, cert, unc);
    if (out) fclose(out);
    return 0;
}
