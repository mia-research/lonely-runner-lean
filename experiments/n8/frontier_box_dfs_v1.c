/* E832: exact box certificates that no carve of [1,7] exists, depth-first refinement.
   Box: rho_i in [n_i/D, (n_i+1)/D], i = 1..6 standing for rho_2..rho_7 (non-decreasing selection required).  A rational R0 = r/2^20 in [1,7] is clear for the box when
   R0 * [n_i/D, (n_i+1)/D] lies in one closed gap [8j+1, 8j+7] for every i (integer test, exact).  Candidates for R0 come from the intersection of the six
   feasible-interval unions in long double, then every candidate is VERIFIED with integers; a box is certified only by the integer test.
   Root boxes: D0 = 1, n_6 in [lo7, hi7), n_i >= 1, n_1 <= ... <= n_6.  Uncertified boxes are halved in every coordinate (children with no non-decreasing
   selection dropped) down to D = Dmax; uncertified leaves at Dmax are counted and written.
   usage: lo7 hi7 Dmax [leaf file] */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
#define GQ (1 << 20)
typedef struct { long double a, b; } iv;
static ll roots = 0, leaves = 0, nodes = 0, cert_by_depth[16];
static int Dmax; static FILE *leaf_out;
static int exact_clear(ll r, int n, int D) {
    ll t = r * n, u = r * (n + 1), base = (ll)GQ * D;
    if (t < base) return 0;
    ll j = (t - base) / (8 * base);
    return u <= (8 * j + 7) * base;
}
static int sorted_feasible(const int *n) {
    int x = n[0];
    for (int i = 0; i < 6; i++) { if (n[i] > x) x = n[i]; if (x > n[i] + 1) return 0; }
    return 1;
}
static int certified(const int *n, int D) {
    iv cur[64], nxt[64]; int nc = 1; cur[0].a = 1.0L; cur[0].b = 7.0L;
    for (int i = 5; i >= 0 && nc; i--) {
        long double a = (long double)n[i] / D, b = (long double)(n[i] + 1) / D;
        iv fe[64]; int nf = 0;
        for (int j = 0; 8 * j + 1 <= 7.0L * b + 1; j++) {
            long double lo = (8 * j + 1) / a, hi = (8 * j + 7) / b;
            if (lo > hi) continue;
            if (lo > 7.0L) break;
            if (hi < 1.0L) continue;
            if (nf < 64) { fe[nf].a = lo; fe[nf].b = hi; nf++; }
        }
        int nn = 0;
        for (int p = 0; p < nc; p++) for (int q = 0; q < nf; q++) {
            long double lo = cur[p].a > fe[q].a ? cur[p].a : fe[q].a, hi = cur[p].b < fe[q].b ? cur[p].b : fe[q].b;
            if (lo <= hi && nn < 64) { nxt[nn].a = lo; nxt[nn].b = hi; nn++; }
        }
        for (int p = 0; p < nn; p++) cur[p] = nxt[p];
        nc = nn;
    }
    for (int p = 0; p < nc; p++) {
        long double mid = (cur[p].a + cur[p].b) / 2;
        ll r0 = (ll)(mid * GQ);
        for (int dr = 0; dr <= 1; dr++) {
            ll r = r0 + dr;
            if (r < (ll)GQ || r > 7LL * GQ) continue;
            int ok = 1;
            for (int i = 0; i < 6; i++) if (!exact_clear(r, n[i], D)) { ok = 0; break; }
            if (ok) return 1;
        }
    }
    return 0;
}
static void refine(const int *n, int D, int depth) {
    nodes++;
    if (certified(n, D)) { cert_by_depth[depth]++; return; }
    if (D >= Dmax) { leaves++; if (leaf_out) fprintf(leaf_out, "%d %d %d %d %d %d %d\n", D, n[0], n[1], n[2], n[3], n[4], n[5]); return; }
    for (int m = 0; m < 64; m++) {
        int c[6];
        for (int i = 0; i < 6; i++) c[i] = 2 * n[i] + ((m >> i) & 1);
        if (!sorted_feasible(c)) continue;
        refine(c, 2 * D, depth + 1);
    }
}
int main(int argc, char **argv) {
    int lo7 = atoi(argv[1]), hi7 = atoi(argv[2]); Dmax = atoi(argv[3]);
    leaf_out = argc > 4 ? fopen(argv[4], "w") : NULL;
    int n[6];
    if (argc > 5) {   /* refine the leaves of an earlier run: lines 'D n0..n5' */
        FILE *in = fopen(argv[5], "r"); int D0;
        while (fscanf(in, "%d %d %d %d %d %d %d", &D0, n, n + 1, n + 2, n + 3, n + 4, n + 5) == 7) { roots++; refine(n, D0, 0); }
        printf("refined leaves of %s to depth cap D=%d: input leaves %lld, nodes tested %lld, uncertified leaves at the cap %lld\n", argv[5], Dmax, roots, nodes, leaves);
        if (leaf_out) fclose(leaf_out); return 0;
    }
    for (n[5] = lo7; n[5] < hi7; n[5]++)
    for (n[4] = 1; n[4] <= n[5]; n[4]++)
    for (n[3] = 1; n[3] <= n[4]; n[3]++)
    for (n[2] = 1; n[2] <= n[3]; n[2]++)
    for (n[1] = 1; n[1] <= n[2]; n[1]++)
    for (n[0] = 1; n[0] <= n[1]; n[0]++) { roots++; refine(n, 1, 0); }
    printf("top reading lower corner in [%d,%d), depth cap D=%d: root boxes %lld, nodes tested %lld, uncertified leaves at the cap %lld\n", lo7, hi7, Dmax, roots, nodes, leaves);
    printf("certified at depth (D=1,2,4,...):"); for (int d = 0; d < 11; d++) printf(" %lld", cert_by_depth[d]); printf("\n");
    if (leaf_out) fclose(leaf_out);
    return 0;
}
