/* Certificate emitter for AbsU5 (E29 tree, checker-compatible).  States = inclusion-minimal masks (8014), instants
   = runner 1's 210.  Node with r runners left (r = 3 at depth 1, r = 2 at depth 2):
     F  = states admissible in every class (block >= |X_c| - 2(r-1) members of X_c),
     D  = U-maximal members of F (relative dominance), l = uncovered instant with fewest blockers in D,
     K  = D intersect blk[l]  (kept children),
     cs = greedy class list such that blk[l] AND (intersection of adm_c over cs) is inside K union dom(K),
          where dom(K) = states good on all of U AND M_k for some k in K (computed over all states).
   Leaves (r = 1): checked as "no state blocks all of U" (AND of blk over U is empty).
   Output:  A k0 l ncs cs... nK          (depth-1 node for root child k0; then nK B-lines)
            B k  l ncs cs... nK K...      (depth-2 node for kept child k)
   Root: l0 = first member of the fullest class; root children = all blockers of l0.
   v2: depth-1 nodes that fail pair-type feasibility are emitted as  P k0 w_1..w_56  (for the i-th type multiset
   t1<=t2<=t3 in lexicographic order, w_i = a class whose uncovered set is not coverable by pairs of differences
   (c t_j)^{-1}); needs the state types (rho mod 7) from the prep file.
   Usage: seven_cert_emit_v2 input.txt lo hi > cert */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define W 4
static int NI, NM, NC, SW; static int *cls, *s1v, *colv; static uint64_t (*M)[W]; static uint64_t (*CM)[W];
static int cmem[64][8], ncm[64];
static uint64_t *blk, *gd, ALLmask_last; static int *typ; static int inv7[7] = {0, 1, 4, 5, 2, 3, 6};
static long long nodesP;
static inline int pc(const uint64_t *a) { return __builtin_popcountll(a[0]) + __builtin_popcountll(a[1]) + __builtin_popcountll(a[2]) + __builtin_popcountll(a[3]); }
static inline int tb(const uint64_t *U, int i) { return U[i / 64] >> (i % 64) & 1; }
static void setall(uint64_t *S) { for (int w = 0; w < SW; w++) S[w] = ~0ULL; S[SW - 1] = ALLmask_last; }
/* states blocking >= m of the list xs (n items) */
static void atleast(const int *xs, int n, int m, uint64_t *out) {
  if (m <= 0) { setall(out); return; }
  if (n < m) { memset(out, 0, 8 * SW); return; }
  uint64_t *a = malloc(8 * SW), *b = malloc(8 * SW);
  atleast(xs + 1, n - 1, m - 1, a); atleast(xs + 1, n - 1, m, b);
  const uint64_t *B = blk + (size_t)xs[0] * SW;
  for (int w = 0; w < SW; w++) out[w] = (B[w] & a[w]) | b[w];
  free(a); free(b);
}
static void admc(const uint64_t *U, int r, int c, uint64_t *out) {
  int xs[8], n = 0; for (int k = 0; k < ncm[c]; k++) if (tb(U, cmem[c][k])) xs[n++] = cmem[c][k];
  atleast(xs, n, n - 2 * (r - 1), out);
}
static void domk(const uint64_t *U, int k, uint64_t *out) {
  setall(out);
  for (int x = 0; x < NI; x++) if (tb(U, x) && tb(M[k], x)) { const uint64_t *G = gd + (size_t)x * SW; for (int w = 0; w < SW; w++) out[w] &= G[w]; }
}
static long long nodesA, nodesB, leaves, sumcs, sumK;
static int pm(int x, int d) { return (1 << x) | (1 << ((x + d) % 7)); }
static int coverable3(int X, int a, int b, int c) {
  for (int x = 0; x < 7; x++) for (int y = 0; y < 7; y++) for (int z = 0; z < 7; z++) if ((X & ~(pm(x, a) | pm(y, b) | pm(z, c))) == 0) return 1;
  return 0;
}
static int classX7(const uint64_t *U, int c) { int X = 0; for (int k = 0; k < ncm[c]; k++) { int i = cmem[c][k]; if (tb(U, i)) X |= 1 << s1v[i]; } return X; }
static int ccolc(int c) { return colv[cmem[c][0]]; }
/* returns 1 and fills w[56] if every type multiset has a failing class */
static int type_infeasible(const uint64_t *U, int *w) {
  int idx = 0;
  for (int t1 = 1; t1 < 7; t1++) for (int t2 = t1; t2 < 7; t2++) for (int t3 = t2; t3 < 7; t3++) {
    int found = -1;
    for (int c = 0; c < NC && found < 0; c++) { int cc = ccolc(c);
      if (!coverable3(classX7(U, c), inv7[(cc * t1) % 7], inv7[(cc * t2) % 7], inv7[(cc * t3) % 7])) found = c; }
    if (found < 0) return 0;
    w[idx++] = found;
  }
  return 1;
}
static int leaf_ok(const uint64_t *U) {
  uint64_t *S = malloc(8 * SW); setall(S);
  for (int x = 0; x < NI; x++) if (tb(U, x)) { const uint64_t *B = blk + (size_t)x * SW; for (int w = 0; w < SW; w++) S[w] &= B[w]; }
  int z = 1; for (int w = 0; w < SW; w++) if (S[w]) z = 0;
  free(S); return z;
}
/* returns 0 on failure */
static int node(const uint64_t *U, int r, int self, FILE *out, char tag) {
  if (r == 3) { int w[56]; if (type_infeasible(U, w)) { fprintf(out, "P %d", self); for (int i = 0; i < 56; i++) fprintf(out, " %d", w[i]); fprintf(out, "\n"); nodesP++; return 1; } }
  uint64_t *F = malloc(8 * SW), *T = malloc(8 * SW);
  setall(F);
  uint64_t admall[64][200]; /* per-class admissible sets (SW <= 200) */
  for (int c = 0; c < NC; c++) { admc(U, r, c, admall[c]); for (int w = 0; w < SW; w++) F[w] &= admall[c][w]; }
  /* D: U-maximal members of F */
  int na = 0; for (int w = 0; w < SW; w++) na += __builtin_popcountll(F[w]);
  int *al = malloc(sizeof(int) * (na + 1)), n0 = 0;
  for (int w = 0; w < SW; w++) { uint64_t x = F[w]; while (x) { al[n0++] = w * 64 + __builtin_ctzll(x); x &= x - 1; } }
  uint64_t (*Bk)[W] = malloc(sizeof(uint64_t[W]) * (n0 + 1)); int *pcs = malloc(sizeof(int) * (n0 + 1)), *ord = malloc(sizeof(int) * (n0 + 1));
  for (int i = 0; i < n0; i++) { for (int q = 0; q < W; q++) Bk[i][q] = U[q] & ~M[al[i]][q]; pcs[i] = pc(Bk[i]); }
  { int cnt[260] = {0}, pos[260], acc = 0; for (int i = 0; i < n0; i++) cnt[pcs[i]]++;
    for (int p = 259; p >= 0; p--) { pos[p] = acc; acc += cnt[p]; } for (int i = 0; i < n0; i++) ord[pos[pcs[i]]++] = i; }
  int *keep = malloc(sizeof(int) * (n0 + 1)), nk = 0;
  for (int a = 0; a < n0; a++) { int i = ord[a], dom = 0;
    for (int b = 0; b < nk && !dom; b++) { int k = keep[b];
      if (((Bk[i][0] & ~Bk[k][0]) | (Bk[i][1] & ~Bk[k][1]) | (Bk[i][2] & ~Bk[k][2]) | (Bk[i][3] & ~Bk[k][3])) == 0) dom = 1; }
    if (!dom) keep[nk++] = i; }
  uint64_t *D = calloc(SW, 8); for (int b = 0; b < nk; b++) { int s = al[keep[b]]; D[s / 64] |= 1ULL << (s % 64); }
  /* branching instant */
  int l = -1, best = 1 << 30;
  for (int x = 0; x < NI; x++) if (tb(U, x)) { int n = 0; const uint64_t *B = blk + (size_t)x * SW; for (int w = 0; w < SW; w++) n += __builtin_popcountll(D[w] & B[w]); if (n < best) { best = n; l = x; } }
  if (l < 0) { fprintf(stderr, "COVER FOUND\n"); return 0; }
  const uint64_t *Bl = blk + (size_t)l * SW;
  int *K = malloc(sizeof(int) * (best + 1)), nK = 0;
  for (int w = 0; w < SW; w++) { uint64_t x = D[w] & Bl[w]; while (x) { K[nK++] = w * 64 + __builtin_ctzll(x); x &= x - 1; } }
  /* covered = bits(K) | dom(K) */
  uint64_t *cov = calloc(SW, 8), *dk = malloc(8 * SW);
  for (int i = 0; i < nK; i++) { cov[K[i] / 64] |= 1ULL << (K[i] % 64); domk(U, K[i], dk); for (int w = 0; w < SW; w++) cov[w] |= dk[w]; }
  /* greedy class list */
  uint64_t *cand = malloc(8 * SW); for (int w = 0; w < SW; w++) cand[w] = Bl[w];
  int cs[64], ncs = 0, used[64] = {0};
  for (;;) {
    int bad = 0; for (int w = 0; w < SW; w++) bad += __builtin_popcountll(cand[w] & ~cov[w]);
    if (!bad) break;
    int bc = -1, bv = -1;
    for (int c = 0; c < NC; c++) if (!used[c]) { int v = 0; for (int w = 0; w < SW; w++) v += __builtin_popcountll(cand[w] & ~cov[w] & ~admall[c][w]); if (v > bv) { bv = v; bc = c; } }
    if (bv <= 0) { fprintf(stderr, "greedy stuck (bad %d)\n", bad); return 0; }
    used[bc] = 1; cs[ncs++] = bc; for (int w = 0; w < SW; w++) cand[w] &= admall[bc][w];
  }
  fprintf(out, "%c %d %d %d", tag, self, l, ncs); for (int i = 0; i < ncs; i++) fprintf(out, " %d", cs[i]); fprintf(out, " %d", nK);
  if (tag == 'B') for (int i = 0; i < nK; i++) fprintf(out, " %d", K[i]);
  fprintf(out, "\n");
  if (tag == 'A') nodesA++; else nodesB++;
  sumcs += ncs; sumK += nK;
  int ok = 1;
  for (int i = 0; i < nK && ok; i++) {
    uint64_t V[W]; for (int q = 0; q < W; q++) V[q] = U[q] & M[K[i]][q];
    if (r == 3) ok = node(V, 2, K[i], out, 'B');
    else { leaves++; if (!leaf_ok(V)) { fprintf(stderr, "leaf fails\n"); ok = 0; } }
  }
  free(F); free(T); free(al); free(Bk); free(pcs); free(ord); free(keep); free(D); free(K); free(cov); free(dk); free(cand);
  return ok;
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d", &NI, &NM, &NC) != 3) return 1;
  cls = malloc(sizeof(int) * NI); s1v = malloc(sizeof(int) * NI); colv = malloc(sizeof(int) * NI);
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &cls[i]) != 1) return 1;
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &s1v[i]) != 1) return 1;
  for (int i = 0; i < NI; i++) if (fscanf(f, "%d", &colv[i]) != 1) return 1;
  M = malloc(sizeof(uint64_t[W]) * NM);
  for (int i = 0; i < NM; i++) for (int w = 0; w < W; w++) if (fscanf(f, "%llu", (unsigned long long *)&M[i][w]) != 1) return 1;
  for (int i = 0; i < NM; i++) for (int c = 0; c < NC; c++) { int v; if (fscanf(f, "%d", &v) != 1) return 1; }
  typ = malloc(sizeof(int) * NM); for (int i = 0; i < NM; i++) if (fscanf(f, "%d", &typ[i]) != 1) return 1;
  CM = calloc(NC, sizeof(uint64_t[W]));
  for (int i = 0; i < NI; i++) { CM[cls[i]][i / 64] |= 1ULL << (i % 64); cmem[cls[i]][ncm[cls[i]]++] = i; }
  SW = (NM + 63) / 64; ALLmask_last = (NM % 64) ? ((1ULL << (NM % 64)) - 1) : ~0ULL;
  blk = calloc((size_t)NI * SW, 8); gd = calloc((size_t)NI * SW, 8);
  for (int x = 0; x < NI; x++) for (int s = 0; s < NM; s++) { if (!tb(M[s], x)) blk[(size_t)x * SW + s / 64] |= 1ULL << (s % 64); else gd[(size_t)x * SW + s / 64] |= 1ULL << (s % 64); }
  int best = 0; for (int c = 0; c < NC; c++) if (pc(CM[c]) > pc(CM[best])) best = c;
  int l0 = cmem[best][0];
  int lo = atoi(argv[2]), hi = atoi(argv[3]), q = 0, ok = 1;
  uint64_t U[W] = {0}; for (int i = 0; i < NI; i++) U[i / 64] |= 1ULL << (i % 64);
  fprintf(stdout, "ROOT %d\n", l0);
  for (int s = 0; s < NM && ok; s++) if (!tb(M[s], l0)) {
    if (q >= lo && q < hi) { uint64_t V[W]; for (int w = 0; w < W; w++) V[w] = U[w] & M[s][w]; ok = node(V, 3, s, stdout, 'A'); }
    q++;
  }
  fprintf(stderr, "range [%d,%d) of %d: P %lld A %lld B %lld leaves %lld avg cs %.2f avg K %.2f ok %d\n", lo, hi, q, nodesP, nodesA, nodesB, leaves,
    (double)sumcs / (nodesA + nodesB), (double)sumK / (nodesA + nodesB), ok);
  return ok ? 0 : 1;
}
