/* enum_profiles.c — enumerate ALL 11! linear orders of ce1068 and emit the EXACT complete set of
 * orbit-profiles (a_1..a_5), a_c = #forward arcs of C_11 arc-class c. This makes the 2-orbit search
 * rigorous: a 2-orbit 2/3-cert exists iff two achievable profiles are antiparallel about (22/3)*1.
 * Output (stdout): one line "a1 a2 a3 a4 a5" per distinct achievable profile.
 * Build: clang -O2 -o enum_profiles enum_profiles.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <sys/time.h>
#include <unistd.h>

/* ---- progress reporting (stderr only — stdout, i.e. the profile list, is untouched) --
 * 11! permutations takes tens of seconds to a couple of minutes: a live one-line counter
 * on a terminal, a line every 15 s when redirected to a file, nothing under PROGRESS=0. */
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

#define N 11
static const char* rows[N] = {
 "01111100000","00110100011","00011100110","00001110011","01000011101",
 "00001001111","11100101000","11110000010","11010011000","10001010101","10100011100"};
static int A[N][N];
static const int sig[N] = {1,2,3,5,10,9,7,0,6,4,8};
static int arcU[64], arcV[64], arcC[64], E=0;   /* arcs + class */
static unsigned char seen[248832];              /* 12^5 profile keys */

int main(void){
    pr_init();
    for(int i=0;i<N;i++) for(int j=0;j<N;j++) A[i][j]=rows[i][j]-'0';
    /* arcs */
    int idx[N][N]; for(int i=0;i<N;i++) for(int j=0;j<N;j++) idx[i][j]=-1;
    for(int u=0;u<N;u++) for(int v=0;v<N;v++) if(A[u][v]){ arcU[E]=u; arcV[E]=v; idx[u][v]=E; arcC[E]=-1; E++; }
    /* classes = sigma-orbits of arcs */
    int nc=0;
    for(int e=0;e<E;e++){ if(arcC[e]>=0) continue; int cid=nc++; int u=arcU[e],v=arcV[e];
        for(int t=0;t<N;t++){ int ee=idx[u][v]; arcC[ee]=cid; u=sig[u]; v=sig[v]; } }
    fprintf(stderr,"E=%d classes=%d\n",E,nc);

    /* Heap's algorithm over perm[0..10]; recompute profile each perm */
    int perm[N]; for(int i=0;i<N;i++) perm[i]=i;
    int c[N]; memset(c,0,sizeof c);
    long count=0, distinct=0;
    /* helper as macro to record current perm's profile */
    #define RECORD() do{ int pos[N]; for(int r=0;r<N;r++) pos[perm[r]]=r; \
        int a0=0,a1=0,a2=0,a3=0,a4=0; \
        for(int e=0;e<E;e++){ if(pos[arcU[e]]<pos[arcV[e]]){ int cc=arcC[e]; \
            if(cc==0)a0++; else if(cc==1)a1++; else if(cc==2)a2++; else if(cc==3)a3++; else a4++; } } \
        long key=((((long)a0)*12+a1)*12+a2)*12+a3; key=key*12+a4; \
        if(!seen[key]){ seen[key]=1; distinct++; } count++; \
        if(!(count & 0xFFFFF) && pr_due()) \
            pr_report("orders %ld/39916800 (%.0f%%), %ld distinct profiles  %.0fs", \
                      count, 100.0*count/39916800.0, distinct, pr_now()-pr_t0); }while(0)

    RECORD();
    int i=0;
    while(i<N){
        if(c[i]<i){
            if(i%2==0){ int t=perm[0]; perm[0]=perm[i]; perm[i]=t; }
            else      { int t=perm[c[i]]; perm[c[i]]=perm[i]; perm[i]=t; }
            RECORD();
            c[i]++; i=0;
        } else { c[i]=0; i++; }
    }
    pr_end();
    fprintf(stderr,"perms=%ld distinct-profiles=%ld\n",count,distinct);
    for(long key=0;key<248832;key++) if(seen[key]){
        long k=key; int a4=k%12; k/=12; int a3=k%12; k/=12; int a2=k%12; k/=12; int a1=k%12; k/=12; int a0=k%12;
        printf("%d %d %d %d %d\n",a0,a1,a2,a3,a4);
    }
    return 0;
}
