/* hs3fas.c — independent check that minFAS == minHS3 (min 3-cycle hitting set) for
 * every tournament in a McKay .txt catalogue (upper-triangle bits, one per line).
 *
 * FAS   = C(n,2) - MAS, MAS via Held-Karp 2^n DP (exact).
 * HS3   = min # arcs hitting every directed 3-cycle, via exact branch-and-bound.
 * We always have HS3 <= FAS; report every tournament where HS3 < FAS (the interesting
 * refutations) and the totals.  Decoding matches HittingSet.R::parseTournaments:
 * lower triangle in COLUMN-MAJOR order, arc i->j (i>j) iff bit==0, else j->i.
 *
 * Build: cc -O3 -o hs3fas hs3fas.c
 * Usage: ./hs3fas catalogue.txt n
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <sys/time.h>
#include <unistd.h>

/* ---- progress reporting (stderr only — stdout, i.e. the result, is untouched) -------
 * The n = 10 catalogue is 9.7M tournaments and takes minutes, so say what is happening:
 * a live one-line counter on a terminal, a line every 15 s when redirected to a file,
 * and nothing at all under PROGRESS=0.  Costs one clock read per tournament. */
static int pr_on, pr_tty; static double pr_last, pr_t0;
static double pr_now(void){ struct timeval tv; gettimeofday(&tv, 0); return tv.tv_sec + 1e-6 * tv.tv_usec; }
static void pr_init(void){ const char *e = getenv("PROGRESS");
    pr_on = !(e && !strcmp(e, "0")); pr_tty = isatty(2); pr_t0 = pr_last = pr_now(); }
static int pr_due(void){ if (!pr_on) return 0; double t = pr_now();
    if (t - pr_last < (pr_tty ? 0.5 : 15.0)) return 0; pr_last = t; return 1; }
static void pr_report(const char *fmt, ...){ va_list ap; va_start(ap, fmt);
    if (pr_tty) fputc('\r', stderr); fputs("  ", stderr); vfprintf(stderr, fmt, ap);
    if (!pr_tty) fputc('\n', stderr); fflush(stderr); va_end(ap); }
static void pr_end(void){ if (pr_on && pr_tty) fputc('\n', stderr); }

static int n, C;
static int inmask[16];               /* inmask[v] = bitmask of u with u->v */
static int Adj[16][16];              /* Adj[u][v]=1 iff u->v */
static int arcid[16][16];            /* index of the (present) arc between u,v */
static uint64_t trimask[512];        /* each cyclic triangle: 3-arc bitmask */
static int ntri;
static int f[1 << 15];

static int mas(void){                /* max acyclic subgraph size */
    int FULL = (1 << n) - 1;
    f[0] = 0;
    for (int S = 1; S <= FULL; S++){
        int best = 0;
        for (int v = 0; v < n; v++) if (S >> v & 1){
            int prev = S ^ (1 << v);
            int val = f[prev] + __builtin_popcount(inmask[v] & prev);
            if (val > best) best = val;
        }
        f[S] = best;
    }
    return f[FULL];
}

static int bestHS;
static long bbnodes;
static long NODELIM = 20000000L;      /* backstop; flag instance if exceeded */
static int hardflag;
static void bb(uint64_t hit, int sz){
    if (sz >= bestHS) return;
    if (++bbnodes > NODELIM){ hardflag = 1; return; }
    /* per-node lower bound: greedy arc-disjoint packing of the UNCOVERED triangles
     * (arcs disjoint from `hit` and from each other) — any completion needs >= lb more. */
    int t = -1, lb = 0; uint64_t used = hit;
    for (int i = 0; i < ntri; i++) if (!(hit & trimask[i])){
        if (t < 0) t = i;                       /* first uncovered triangle to branch on */
        if (!(used & trimask[i])){ used |= trimask[i]; lb++; }
    }
    if (t < 0){ bestHS = sz; return; }          /* all covered */
    if (sz + lb >= bestHS) return;              /* packing bound prune */
    uint64_t m = trimask[t];
    while (m){ uint64_t a = m & (~m + 1); m ^= a; bb(hit | a, sz + 1); }
}

/* greedy arc-disjoint 3-cycle packing: a valid LOWER bound on HS3 (each packed
 * triangle needs its own hitting arc).  If it equals FAS, then HS3 == FAS is
 * sandwiched (packing <= HS3 <= FAS), no search needed. */
static int pack_lb(void){
    uint64_t used = 0; int cnt = 0;
    for (int i = 0; i < ntri; i++)
        if (!(used & trimask[i])){ used |= trimask[i]; cnt++; }
    return cnt;
}

static void build_arcs_tris(void){
    int id = 0;
    for (int u = 0; u < n; u++) for (int v = u + 1; v < n; v++){
        arcid[u][v] = arcid[v][u] = id++;   /* one arc per unordered pair */
    }
    ntri = 0;
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) for (int c = b + 1; c < n; c++){
        /* cyclic iff each of a,b,c has out-degree 1 within {a,b,c} */
        int oa = Adj[a][b] + Adj[a][c], ob = Adj[b][a] + Adj[b][c], oc = Adj[c][a] + Adj[c][b];
        if (oa == 1 && ob == 1 && oc == 1){
            trimask[ntri++] = (1ULL << arcid[a][b]) | (1ULL << arcid[b][c]) | (1ULL << arcid[a][c]);
        }
    }
}

static void decode(const char *bits){
    memset(Adj, 0, sizeof Adj);
    for (int v = 0; v < n; v++) inmask[v] = 0;
    int k = 0;
    for (int j = 0; j < n; j++) for (int i = j + 1; i < n; i++){   /* lower tri, column-major */
        int b = bits[k++] - '0';
        if (b == 0){ Adj[i][j] = 1; inmask[j] |= (1 << i); }        /* i->j */
        else       { Adj[j][i] = 1; inmask[i] |= (1 << j); }        /* j->i */
    }
}

int main(int argc, char **argv){
    if (argc < 3){ fprintf(stderr, "usage: %s file n\n", argv[0]); return 1; }
    FILE *fp = fopen(argv[1], "r");
    if (!fp){ perror("open"); return 1; }
    n = atoi(argv[2]); C = n * (n - 1) / 2;
    char line[128];
    long total = 0, mism = 0, hard = 0;
    pr_init();
    long est = 0;                       /* expected #tournaments: every line is C bits + '\n' */
    if (!fseek(fp, 0, SEEK_END)){ est = ftell(fp) / (C + 1); rewind(fp); }
    fprintf(stderr, "hs3fas: %s, n=%d, %ld tournaments to check\n", argv[1], n, est);
    while (fgets(line, sizeof line, fp)){
        int L = strlen(line);
        while (L && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        if (L != C) continue;
        decode(line);
        int fas = C - mas();
        build_arcs_tris();
        total++;
        if (pr_due())
            pr_report("hs3fas n=%d: %ld/%ld tournaments (%.1f%%), %ld with HS3<FAS, %ld hard  %.0fs",
                      n, total, est, est ? 100.0 * total / est : 0.0, mism, hard, pr_now() - pr_t0);
        if (pack_lb() == fas) continue;     /* HS3 sandwiched == FAS, no search */
        bestHS = fas + 1; bbnodes = 0; hardflag = 0;
        bb(0, 0);
        if (hardflag){
            hard++;
            if (hard <= 20) printf("HARD idx %ld (B&B node limit, FAS=%d): bits=%s\n", total, fas, line);
            continue;
        }
        int hs3 = bestHS;
        if (hs3 != fas){
            mism++;
            if (mism <= 20) printf("MISMATCH idx %ld: FAS=%d HS3=%d  bits=%s\n", total, fas, hs3, line);
        }
    }
    fclose(fp);
    pr_end();
    printf("n=%d: %ld tournaments; %ld with HS3<FAS; %ld HARD (unresolved) => minFAS %s minHS3\n",
           n, total, mism, hard, (mism==0 && hard==0) ? "== for ALL" :
           mism ? "!= (see above)" : "== except HARD (need stronger solve)");
    return 0;
}
