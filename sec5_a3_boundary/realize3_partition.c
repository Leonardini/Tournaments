/* realize3_partition.c — THIRD, solver-free confirmation that ce1068 is not 3-realizable.
 * Since alpha*=2/3 and every arc lies on a 3-cycle, a 3-voter majority realization needs every arc
 * forward in EXACTLY 2 of 3 orders  <=>  the three orders' backward-sets PARTITION all 55 arcs
 * (B1 disjoint-union B2 disjoint-union B3 = full).  We enumerate all 11! orders as 55-bit backward
 * masks and look for such a partition. By the C_11 automorphism we fix O1 to its orbit-rep (min mask),
 * and take O1 = the smallest backward set (back<=18, since the three sizes are >=16 and sum to 55).
 * Result: NO partition  =>  not 3-realizable (matches CPLEX + CP-SAT).
 * Build: clang -O3 -o realize3_partition realize3_partition.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define N 11
static const char* rows[N] = {
 "01111100000","00110100011","00011100110","00001110011","01000011101",
 "00001001111","11100101000","11110000010","11010011000","10001010101","10100011100"};
static int A[N][N];
static const int sig[N] = {1,2,3,5,10,9,7,0,6,4,8};
static int arcU[64], arcV[64], E=0, Q[64];        /* arcs + sigma arc-permutation */
static uint64_t FULL;

/* dynamic arrays */
static uint64_t *H=NULL; static long nH=0, capH=0;      /* backward masks with back<=23 (O2/O3 pool) */
static uint64_t *O1=NULL; static long nO1=0, capO1=0;   /* orbit-rep masks with back<=18 (O1 pool) */
static void pushH(uint64_t m){ if(nH==capH){capH=capH?capH*2:1<<20; H=realloc(H,capH*8);} H[nH++]=m; }
static void pushO1(uint64_t m){ if(nO1==capO1){capO1=capO1?capO1*2:1<<16; O1=realloc(O1,capO1*8);} O1[nO1++]=m; }

static uint64_t apply_perm(uint64_t m){                 /* mask(sigma o O) from mask(O) */
    uint64_t r=0; for(int e=0;e<E;e++) if(m>>e&1) r|=1ULL<<Q[e]; return r;
}
static int cmp64(const void*a,const void*b){ uint64_t x=*(const uint64_t*)a,y=*(const uint64_t*)b; return x<y?-1:x>y; }
static int inH(uint64_t m){                             /* binary search membership */
    long lo=0,hi=nH-1; while(lo<=hi){ long mid=(lo+hi)>>1; if(H[mid]<m)lo=mid+1; else if(H[mid]>m)hi=mid-1; else return 1; } return 0;
}

int main(int argc,char**argv){
    int NOSYM = (argc>1);                               /* any arg => enumerate ALL back<=18 as O1 (no symmetry) */
    for(int i=0;i<N;i++) for(int j=0;j<N;j++) A[i][j]=rows[i][j]-'0';
    int idx[N][N]; for(int i=0;i<N;i++) for(int j=0;j<N;j++) idx[i][j]=-1;
    for(int u=0;u<N;u++) for(int v=0;v<N;v++) if(A[u][v]){ arcU[E]=u; arcV[E]=v; idx[u][v]=E; E++; }
    for(int e=0;e<E;e++) Q[e]=idx[sig[arcU[e]]][sig[arcV[e]]];
    FULL=(E==64)?~0ULL:((1ULL<<E)-1);
    fprintf(stderr,"E=%d\n",E);

    long hist[64]; memset(hist,0,sizeof hist);
    int perm[N]; for(int i=0;i<N;i++) perm[i]=i;
    int c[N]; memset(c,0,sizeof c);
    long total=0;
    #define PROC() do{ int pos[N]; for(int r=0;r<N;r++) pos[perm[r]]=r; \
        uint64_t bm=0; for(int e=0;e<E;e++) if(pos[arcU[e]]>pos[arcV[e]]) bm|=1ULL<<e; \
        int b=__builtin_popcountll(bm); hist[b]++; total++; \
        if(b<=23) pushH(bm); \
        if(b<=18){ if(NOSYM){ pushO1(bm); } else { uint64_t mn=bm,q=bm; for(int t=1;t<N;t++){ q=apply_perm(q); if(q<mn)mn=q; } if(mn==bm) pushO1(bm); } } \
    }while(0)
    PROC();
    int i=0;
    while(i<N){
        if(c[i]<i){ if(i%2==0){int t=perm[0];perm[0]=perm[i];perm[i]=t;} else {int t=perm[c[i]];perm[c[i]]=perm[i];perm[i]=t;} PROC(); c[i]++; i=0; }
        else { c[i]=0; i++; }
    }
    fprintf(stderr,"total orders=%ld  |O2/O3 pool (back<=23)|=%ld  |O1 orbit-reps (back<=18)|=%ld\n",total,nH,nO1);
    fprintf(stderr,"back-count histogram (min back=%d => MAS=%d):\n", 0, 0);
    for(int b=0;b<=55;b++) if(hist[b]) fprintf(stderr,"  back=%2d : %ld\n",b,hist[b]);

    qsort(H,nH,8,cmp64);
    /* search: O1 (orbit-rep, smallest) ; O2,O3 partition its forward set, back nondecreasing */
    long checks=0;
    for(long a=0;a<nO1;a++){
        uint64_t m1=O1[a]; int b1=__builtin_popcountll(m1); uint64_t F1=FULL&~m1;
        for(long j=0;j<nH;j++){
            uint64_t m2=H[j];
            if(m2 & m1) continue;                         /* need B2 disjoint from B1 */
            int b2=__builtin_popcountll(m2); if(b2<b1) continue;
            uint64_t m3=F1 & ~m2; int b3=__builtin_popcountll(m3);
            if(b3<b2) continue;
            checks++;
            if(inH(m3)){
                fprintf(stderr,"\n*** 3-REALIZATION FOUND (partition) *** backs=(%d,%d,%d)\n",b1,b2,b3);
                printf("FOUND m1=%llx m2=%llx m3=%llx backs=%d,%d,%d\n",(unsigned long long)m1,(unsigned long long)m2,(unsigned long long)m3,b1,b2,b3);
                return 0;
            }
        }
    }
    fprintf(stderr,"\ncandidate checks=%ld\n",checks);
    printf("NO PARTITION EXISTS => ce1068 is NOT 3-realizable (third, solver-free confirmation).\n");
    return 0;
}
