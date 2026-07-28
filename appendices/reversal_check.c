/* reversal_check.c — for each input tournament (gentourng bit-string; intended:
 * the 3-realizable-but-not-margin-1 hits), compute
 *   (1) U = forced-unanimous arcs: e with 4-label CSP UNSAT when label(e) is
 *       restricted to {1,2,3} (i.e. no 3-realization dissents on e);
 *   (2) for each e in U, whether T with e reversed is 3-realizable (4-label CSP).
 * Conjecture (Leonid): (1) is nonempty for every such T and every reversal in
 * (2) is non-realizable.  Output: one line per tournament
 *   OK <#forced> <line>            conjecture holds here
 *   NOFORCED <line>                no forced-unanimous arc  (finding!)
 *   CEX <arc> <line>               forced arc whose reversal stays realizable (!)
 * Tallies to stderr.  Usage: reversal_check n < hits
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int n, m;
#define MAXN 14
#define MAXM (MAXN*(MAXN-1)/2)
#define MAXT (MAXN*(MAXN-1)*(MAXN-2)/6)

static int A[MAXN][MAXN];
static int aidx[MAXN][MAXN];
static int arc_u[MAXM], arc_v[MAXM];
static int ntri, tri_kind[MAXT], tri_arc[MAXT][3];
static int occ[MAXM][MAXN*3], nocc[MAXM];

static void build(void) {
    int idx = 0;
    for (int i = 0; i < n; i++) for (int j = i+1; j < n; j++) {
        if (A[i][j]) { aidx[i][j] = idx; arc_u[idx] = i; arc_v[idx] = j; }
        else         { aidx[j][i] = idx; arc_u[idx] = j; arc_v[idx] = i; }
        idx++;
    }
    memset(nocc, 0, sizeof nocc);
    ntri = 0;
    for (int x = 0; x < n; x++) for (int y = x+1; y < n; y++) for (int z = y+1; z < n; z++) {
        int ab = A[x][y], bc = A[y][z], ca = A[z][x];
        int t = ntri++;
        if ((ab && bc && ca) || (!ab && !bc && !ca)) {
            tri_kind[t] = 1;
            if (ab) { tri_arc[t][0]=aidx[x][y]; tri_arc[t][1]=aidx[y][z]; tri_arc[t][2]=aidx[z][x]; }
            else    { tri_arc[t][0]=aidx[y][x]; tri_arc[t][1]=aidx[z][y]; tri_arc[t][2]=aidx[x][z]; }
        } else {
            int v[3] = {x, y, z}, src=-1, snk=-1, mid=-1;
            for (int i = 0; i < 3; i++) {
                int wins = 0;
                for (int j = 0; j < 3; j++) if (i != j && A[v[i]][v[j]]) wins++;
                if (wins == 2) src = v[i];
                if (wins == 0) snk = v[i];
            }
            for (int i = 0; i < 3; i++) if (v[i] != src && v[i] != snk) mid = v[i];
            tri_kind[t] = 0;
            tri_arc[t][0] = aidx[src][snk];
            tri_arc[t][1] = aidx[src][mid];
            tri_arc[t][2] = aidx[mid][snk];
        }
        for (int k = 0; k < 3; k++) { int a = tri_arc[t][k]; occ[a][nocc[a]++] = t; }
    }
}

static int prune(unsigned char *mask, int *queue, int qn) {
    static unsigned char inq[MAXT];
    memset(inq, 0, ntri);
    int head = 0;
    for (int i = 0; i < qn; i++) inq[queue[i]] = 1;
    while (head < qn) {
        int t = queue[head++]; inq[t] = 0;
        int a0 = tri_arc[t][0], a1 = tri_arc[t][1], a2 = tri_arc[t][2];
        int m0 = mask[a0], m1 = mask[a1], m2 = mask[a2];
        int n0 = 0, n1 = 0, n2 = 0;
        if (tri_kind[t]) {
            for (int c0 = 1; c0 <= 3; c0++) { if (!((m0>>c0)&1)) continue;
                for (int c1 = 1; c1 <= 3; c1++) { if (c1==c0 || !((m1>>c1)&1)) continue;
                    int c2 = 6 - c0 - c1;
                    if ((m2>>c2)&1) { n0 |= 1<<c0; n1 |= 1<<c1; n2 |= 1<<c2; }
                } }
        } else {
            for (int cs = 0; cs <= 3; cs++) { if (!((m0>>cs)&1)) continue;
                for (int c1 = 0; c1 <= 3; c1++) { if (!((m1>>c1)&1)) continue;
                    for (int c2 = 0; c2 <= 3; c2++) { if (!((m2>>c2)&1)) continue;
                        if (cs != 0 && cs != c1 && cs != c2) continue;
                        if (c1 != 0 && c1 == c2 && cs != c1) continue;
                        n0 |= 1<<cs; n1 |= 1<<c1; n2 |= 1<<c2;
                    } } }
        }
        if (!n0 || !n1 || !n2) return 0;
        int as[3] = {a0, a1, a2}, ns[3] = {n0, n1, n2};
        for (int k = 0; k < 3; k++) {
            if (ns[k] != mask[as[k]]) {
                mask[as[k]] = (unsigned char)ns[k];
                for (int j = 0; j < nocc[as[k]]; j++) {
                    int tt = occ[as[k]][j];
                    if (!inq[tt]) { inq[tt] = 1; queue[qn++] = tt; }
                }
            }
        }
    }
    return 1;
}

static int popc(int x){ int c=0; while(x){c+=x&1;x>>=1;} return c; }

static int dfs(unsigned char *mask, int usedmax) {
    int best = 5, ba = -1;
    for (int a = 0; a < m; a++) {
        int pc = popc(mask[a]);
        if (pc > 1 && pc < best) { best = pc; ba = a; }
    }
    if (ba < 0) return 1;
    int capped = usedmax + 1; if (capped > 3) capped = 3;
    for (int c = 0; c <= capped; c++) {
        if (!((mask[ba]>>c)&1)) continue;
        unsigned char m2[MAXM];
        memcpy(m2, mask, m);
        m2[ba] = (unsigned char)(1 << c);
        int queue[MAXT*8], qn = 0;
        for (int j = 0; j < nocc[ba]; j++) queue[qn++] = occ[ba][j];
        int um = usedmax > c ? usedmax : c;
        if (prune(m2, queue, qn) && dfs(m2, um)) return 1;
    }
    return 0;
}

/* 4-label solve; if force_dissent >= 0, that arc's label is restricted to {1,2,3} */
static int solve4(int force_dissent) {
    unsigned char mask[MAXM];
    for (int a = 0; a < m; a++) mask[a] = 0x0F;
    if (force_dissent >= 0) mask[force_dissent] &= 0x0E;
    /* voter symmetry: arc 0 wlog in {0,1}; if arc0 is the forced arc -> {1} */
    mask[0] &= 0x03;
    int queue[MAXT*8], qn = 0;
    for (int t = 0; t < ntri; t++) queue[qn++] = t;
    if (!prune(mask, queue, qn)) return 0;
    return dfs(mask, 1);
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); m = n*(n-1)/2;
    int stats = (argc > 2 && !strcmp(argv[2], "stats"));
    long ghist[MAXN][2]; memset(ghist, 0, sizeof ghist);   /* [gained][reversal-realizable] */
    char line[256];
    long tot = 0, ok = 0, noforced = 0, cex = 0;
    long forced_hist[8] = {0};
    while (fgets(line, sizeof line, stdin)) {
        if (line[0] == 'R' && line[1] == ' ') memmove(line, line+2, strlen(line+2)+1);
        int k = 0;
        for (int i = 0; i < n; i++) for (int j = i+1; j < n; j++) {
            if (line[k] == '1') { A[i][j] = 1; A[j][i] = 0; }
            else                { A[i][j] = 0; A[j][i] = 1; }
            k++;
        }
        build();
        tot++;
        int nf = 0, bad = -1;
        for (int e = 0; e < m; e++) {
            if (!solve4(e)) {                      /* e forced unanimous */
                nf++;
                int u = arc_u[e], v = arc_v[e];
                int g = 0;                         /* 3-cycles gained on reversal */
                for (int w = 0; w < n; w++) if (w != u && w != v && A[u][w] && A[w][v]) g++;
                A[u][v] = 0; A[v][u] = 1;          /* reverse e */
                build();
                int still = solve4(-1);
                A[u][v] = 1; A[v][u] = 0;          /* restore */
                build();
                if (stats) ghist[g][still ? 1 : 0]++;
                if (still) { bad = e; if (!stats) break; }
            }
        }
        line[m] = 0;
        if (bad >= 0)      { cex++; printf("CEX %d->%d %s\n", arc_u[bad], arc_v[bad], line); }
        else if (nf == 0)  { noforced++; printf("NOFORCED %s\n", line); }
        else               { ok++; forced_hist[nf > 7 ? 7 : nf]++; }
        if (tot % 10000 == 0) fprintf(stderr, "... %ld (ok %ld / noforced %ld / cex %ld)\n", tot, ok, noforced, cex);
    }
    fprintf(stderr, "n=%d: total %ld, conjecture-OK %ld, NOFORCED %ld, CEX %ld\n", n, tot, ok, noforced, cex);
    fprintf(stderr, "forced-arc count histogram (1..6,7+):");
    for (int i = 1; i < 8; i++) fprintf(stderr, " %ld", forced_hist[i]);
    fprintf(stderr, "\n");
    if (stats) {
        fprintf(stderr, "gained-3-cycles histogram over forced arcs (g: kills / survives):\n");
        for (int g = 0; g < n; g++)
            if (ghist[g][0] || ghist[g][1])
                fprintf(stderr, "  g=%d: %ld / %ld\n", g, ghist[g][0], ghist[g][1]);
    }
    return 0;
}
