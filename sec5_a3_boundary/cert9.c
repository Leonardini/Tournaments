/* cert9.c — decide existence of a 9-voter 2/3-certificate: nine linear orders
 * such that every arc of T is forward in >= 6 of them (SAT => alpha*(T) >= 2/3,
 * and for non-transitive T then alpha* = 2/3 exactly).
 *
 * CSP (cert6.c lifted from 6 to 9 voters): label each arc by its dissent set D
 * (voters ranking it backward), |D| <= 3 (130 labels: 1 empty + 9 singletons +
 * 36 pairs + 84 triples).  Per voter i, class {arcs : i in D} must be an
 * inversion set => triple-local conditions:
 *   cyclic triple: the three dissent sets are disjoint TRIPLES partitioning the
 *     nine voters (coverage >= 1 per voter, sizes <= 3, 3*3 = 9 forces this);
 *   transitive triple (s, p1, p2): D(s) subset of D(p1) u D(p2), and
 *     D(p1) n D(p2) subset of D(s).
 * Symmetry: voters S_9-interchangeable; broken by pinning the first cyclic
 * triple's partition to ({0,1,2},{3,4,5},{6,7,8}).
 *
 * Usage: cert9 n < bitstrings ; prints "Y <line>" / "N <line>", tallies stderr.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int n, m;
#define MAXN 14
#define MAXM (MAXN*(MAXN-1)/2)
#define MAXT (MAXN*(MAXN-1)*(MAXN-2)/6)
#define NL 130                    /* 1 empty + 9 singletons + 36 pairs + 84 triples */
#define NTRIP 84

typedef struct { uint64_t w[3]; } Mask;
static inline int  mtest(const Mask *m_, int b){ return (int)((m_->w[b>>6] >> (b&63)) & 1u); }
static inline void mset (Mask *m_, int b){ m_->w[b>>6] |= 1ull << (b&63); }
static inline int  mnone(const Mask *m_){ return !(m_->w[0] | m_->w[1] | m_->w[2]); }
static inline int  meq  (const Mask *a, const Mask *b){
    return a->w[0]==b->w[0] && a->w[1]==b->w[1] && a->w[2]==b->w[2]; }
static inline int  mpopc(const Mask *m_){
    return __builtin_popcountll(m_->w[0]) + __builtin_popcountll(m_->w[1])
         + __builtin_popcountll(m_->w[2]); }
static const Mask MZERO = {{0,0,0}};

static int A[MAXN][MAXN], aidx[MAXN][MAXN];
static int ntri, tri_kind[MAXT], tri_arc[MAXT][3];
static int occ[MAXM][MAXN*3], nocc[MAXM];
static int voterbm[NL];                   /* label -> 9-bit voter set */
static int lbl_of[512];                   /* 9-bit voter set -> label (or -1) */
static int trip_list[NTRIP];              /* labels of the 84 voter-triples */

static void init_labels(void) {
    memset(lbl_of, -1, sizeof lbl_of);
    int l = 0;
    voterbm[l] = 0; lbl_of[0] = l; l++;
    for (int i = 0; i < 9; i++) { voterbm[l] = 1 << i; lbl_of[voterbm[l]] = l; l++; }
    for (int i = 0; i < 9; i++) for (int j = i+1; j < 9; j++) {
        voterbm[l] = (1 << i) | (1 << j); lbl_of[voterbm[l]] = l; l++;
    }
    int nt = 0;
    for (int i = 0; i < 9; i++) for (int j = i+1; j < 9; j++) for (int k = j+1; k < 9; k++) {
        voterbm[l] = (1 << i) | (1 << j) | (1 << k);
        lbl_of[voterbm[l]] = l;
        trip_list[nt++] = l;
        l++;
    }
}

static void build(void) {
    int idx = 0;
    for (int i = 0; i < n; i++) for (int j = i+1; j < n; j++) {
        if (A[i][j]) aidx[i][j] = idx; else aidx[j][i] = idx;
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

static int prune(Mask *mask, int *queue, int qn) {
    static unsigned char inq[MAXT];
    memset(inq, 0, ntri);
    int head = 0;
    for (int i = 0; i < qn; i++) inq[queue[i]] = 1;
    while (head < qn) {
        int t = queue[head++]; inq[t] = 0;
        int a0 = tri_arc[t][0], a1 = tri_arc[t][1], a2 = tri_arc[t][2];
        Mask m0 = mask[a0], m1 = mask[a1], m2 = mask[a2];
        Mask n0 = MZERO, n1 = MZERO, n2 = MZERO;
        if (tri_kind[t]) {                        /* disjoint triple partition */
            for (int i0 = 0; i0 < NTRIP; i0++) { int l0 = trip_list[i0];
                if (!mtest(&m0, l0)) continue;
                int b0 = voterbm[l0];
                for (int i1 = 0; i1 < NTRIP; i1++) { int l1 = trip_list[i1];
                    if (!mtest(&m1, l1)) continue;
                    int b1 = voterbm[l1];
                    if (b0 & b1) continue;
                    int b2 = 0x1FF ^ b0 ^ b1;
                    int l2 = lbl_of[b2];
                    if (mtest(&m2, l2)) { mset(&n0, l0); mset(&n1, l1); mset(&n2, l2); }
                } }
        } else {                                  /* s, p1, p2 */
            for (int ls = 0; ls < NL; ls++) { if (!mtest(&m0, ls)) continue;
                int bs = voterbm[ls];
                for (int l1 = 0; l1 < NL; l1++) { if (!mtest(&m1, l1)) continue;
                    int b1 = voterbm[l1];
                    int need = bs & ~b1;          /* must be inside b2 */
                    int forbid = b1 & ~bs;        /* must avoid b2 */
                    for (int l2 = 0; l2 < NL; l2++) { if (!mtest(&m2, l2)) continue;
                        int b2 = voterbm[l2];
                        if (need & ~b2) continue;             /* D(s) not covered */
                        if (forbid & b2) continue;            /* path pair escapes s */
                        mset(&n0, ls); mset(&n1, l1); mset(&n2, l2);
                    } } }
        }
        if (mnone(&n0) || mnone(&n1) || mnone(&n2)) return 0;
        int as[3] = {a0, a1, a2}; Mask ns[3]; ns[0]=n0; ns[1]=n1; ns[2]=n2;
        for (int k = 0; k < 3; k++) {
            if (!meq(&ns[k], &mask[as[k]])) {
                mask[as[k]] = ns[k];
                for (int j = 0; j < nocc[as[k]]; j++) {
                    int tt = occ[as[k]][j];
                    if (!inq[tt]) { inq[tt] = 1; queue[qn++] = tt; }
                }
            }
        }
        if (qn > MAXT*24) { fprintf(stderr, "queue overflow\n"); exit(1); }
    }
    return 1;
}

static int dfs(Mask *mask) {
    int best = NL + 1, ba = -1;
    for (int a = 0; a < m; a++) {
        int pc = mpopc(&mask[a]);
        if (pc > 1 && pc < best) { best = pc; ba = a; }
    }
    if (ba < 0) return 1;
    for (int l = 0; l < NL; l++) {
        if (!mtest(&mask[ba], l)) continue;
        Mask m2[MAXM];
        memcpy(m2, mask, m * sizeof(Mask));
        m2[ba] = MZERO; mset(&m2[ba], l);
        int queue[MAXT*24], qn = 0;
        for (int j = 0; j < nocc[ba]; j++) queue[qn++] = occ[ba][j];
        if (prune(m2, queue, qn) && dfs(m2)) return 1;
    }
    return 0;
}

static int solve_cert9(void) {
    Mask mask[MAXM];
    Mask FULLM = MZERO;
    for (int l = 0; l < NL; l++) mset(&FULLM, l);
    for (int a = 0; a < m; a++) mask[a] = FULLM;
    /* symmetry: pin the first cyclic triple's partition to {0,1,2},{3,4,5},{6,7,8} */
    for (int t = 0; t < ntri; t++) {
        if (tri_kind[t]) {
            mask[tri_arc[t][0]] = MZERO; mset(&mask[tri_arc[t][0]], lbl_of[0x007]);
            mask[tri_arc[t][1]] = MZERO; mset(&mask[tri_arc[t][1]], lbl_of[0x038]);
            mask[tri_arc[t][2]] = MZERO; mset(&mask[tri_arc[t][2]], lbl_of[0x1C0]);
            break;
        }
    }
    int queue[MAXT*24], qn = 0;
    for (int t = 0; t < ntri; t++) queue[qn++] = t;
    if (!prune(mask, queue, qn)) return 0;
    return dfs(mask);
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); m = n*(n-1)/2;
    init_labels();
    char line[256];
    long tot = 0, yes = 0;
    while (fgets(line, sizeof line, stdin)) {
        if ((line[0] == 'C' || line[0] == 'N' || line[0] == 'R') && strchr(line, ' '))
            memmove(line, strchr(line, ' ') + 1, strlen(strchr(line, ' ')));
        int k = 0;
        for (int i = 0; i < n; i++) for (int j = i+1; j < n; j++) {
            if (line[k] == '1') { A[i][j] = 1; A[j][i] = 0; }
            else                { A[i][j] = 0; A[j][i] = 1; }
            k++;
        }
        line[m] = 0;
        build();
        tot++;
        if (solve_cert9()) { yes++; printf("Y %s\n", line); }
        else printf("N %s\n", line);
        if (tot % 1000 == 0) fprintf(stderr, "... %ld (Y %ld)\n", tot, yes);
    }
    fprintf(stderr, "total %ld: cert9-SAT %ld, UNSAT %ld\n", tot, yes, tot - yes);
    return 0;
}
