/* alpha_fast.c — fast FLOAT alpha* (predictability) for a batch of tournaments, via cutting planes:
 * C weighted-MAS DP oracle + incremental GLPK master LP. Purpose: the self-converse n=11 census —
 * classify alpha*=2/3 vs <2/3 (gap > 0.009, so float to ~1e-7 suffices); the rare alpha*~2/3 hits are
 * re-verified EXACTLY in R (rcdd). alpha* <= MAS/C, so MAS < ceil(2C/3) => alpha* < 2/3 (fast reject).
 *
 * Input : a file, one tournament per line as n in-neighbour bitmasks inm[0..n-1] (arc u->v iff bit u of
 *         inm[v] set). n inferred from the first line (all lines same n). n <= 15.
 * Output: "idx MAS alpha"  per line (alpha = -1 when MAS-rejected, i.e. alpha* < 2/3).
 * Build : clang -O2 -o alpha_fast alpha_fast.c -I/opt/homebrew/include -L/opt/homebrew/lib -lglpk
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <glpk.h>

static int n, C;
static int af[128], at[128];          /* arcs (0-based) */
static double Wm[16][16];
static double *contrib=NULL, *f=NULL; static int *par=NULL;

static double oracle(const double* w, int* order){   /* max forward-weight order for arc weights w[0..C-1] */
    for(int i=0;i<n;i++) for(int j=0;j<n;j++) Wm[i][j]=0.0;
    for(int e=0;e<C;e++) Wm[af[e]][at[e]] = w[e];
    long FULL=(1L<<n)-1;
    for(int v=0;v<n;v++) contrib[v]=0.0;
    for(long S=1;S<=FULL;S++){ int low=__builtin_ctzl((unsigned long)S); long P=S^(1L<<low);
        double* cs=&contrib[S*n]; const double* cp=&contrib[P*n]; const double* wl=Wm[low];
        for(int v=0;v<n;v++) cs[v]=cp[v]+wl[v]; }
    for(long S=0;S<=FULL;S++) f[S]=-1e18; f[0]=0.0;
    for(long S=0;S<=FULL;S++){ if(f[S]<-1e17) continue; double fS=f[S]; const double* cs=&contrib[S*n];
        for(int v=0;v<n;v++){ if((S>>v)&1) continue; long ns=S|(1L<<v); double val=fS+cs[v];
            if(val>f[ns]){ f[ns]=val; par[ns]=v; } } }
    long S=FULL; for(int k=n-1;k>=0;k--){ int v=par[S]; order[k]=v; S^=(1L<<v); }
    return f[FULL];
}

static void add_cut(glp_prob* lp, const int* order){
    int pos[16]; for(int k=0;k<n;k++) pos[order[k]]=k;
    int r=glp_add_rows(lp,1); glp_set_row_bnds(lp,r,GLP_UP,0.0,0.0);
    int ind[130]; double val[130]; int len=0;
    for(int e=0;e<C;e++) if(pos[af[e]]<pos[at[e]]){ len++; ind[len]=e+1; val[len]=1.0; }
    len++; ind[len]=C+1; val[len]=-1.0;               /* -t */
    glp_set_mat_row(lp,r,len,ind,val);
}

static double alpha_star(double tol){
    glp_prob* lp=glp_create_prob(); glp_set_obj_dir(lp,GLP_MIN);
    glp_add_cols(lp,C+1);
    for(int e=1;e<=C;e++){ glp_set_col_bnds(lp,e,GLP_LO,0.0,0.0); glp_set_obj_coef(lp,e,0.0); }
    glp_set_col_bnds(lp,C+1,GLP_FR,0.0,0.0); glp_set_obj_coef(lp,C+1,1.0);   /* t */
    int r=glp_add_rows(lp,1); glp_set_row_bnds(lp,r,GLP_FX,1.0,1.0);          /* sum y = 1 */
    { int ind[130]; double val[130]; for(int e=1;e<=C;e++){ ind[e]=e; val[e]=1.0; } glp_set_mat_row(lp,r,C,ind,val); }
    glp_smcp parm; glp_init_smcp(&parm); parm.msg_lev=GLP_MSG_OFF; parm.presolve=GLP_OFF;
    int order[16], idord[16]; for(int i=0;i<n;i++) idord[i]=i; add_cut(lp,idord);
    double w[128], t=0.0;
    for(int it=0; it<3000; it++){
        glp_simplex(lp,&parm);
        t=glp_get_col_prim(lp,C+1);
        for(int e=0;e<C;e++) w[e]=glp_get_col_prim(lp,e+1);
        double val=oracle(w,order);
        if(val<=t+tol) break;
        add_cut(lp,order);
    }
    glp_delete_prob(lp);
    return t;
}

int main(int argc,char**argv){
    if(argc<2){ fprintf(stderr,"usage: %s inmaskfile\n",argv[0]); return 1; }
    FILE* fp=fopen(argv[1],"r"); if(!fp){ perror(argv[1]); return 1; }
    long idx = (argc>=3) ? strtol(argv[2],NULL,10) : 0;   /* optional idx offset for parallel chunks */
    char* line=NULL; size_t cap=0; ssize_t len; int allocated=0;
    double ones[128], w1[128]; int order[16];
    while((len=getline(&line,&cap,fp))>0){
        long inm[16]; int m=0; char* p=line; char* end;
        while(1){ long v=strtol(p,&end,10); if(end==p) break; if(m<16) inm[m++]=v; p=end; }
        if(m==0) continue;
        if(!allocated){ n=m; C=n*(n-1)/2; long sz=1L<<n;
            contrib=malloc((size_t)sz*n*sizeof(double)); f=malloc((size_t)sz*sizeof(double)); par=malloc((size_t)sz*sizeof(int));
            if(!contrib||!f||!par){ fprintf(stderr,"alloc fail\n"); return 1; } allocated=1; }
        /* build arcs: A[u][v]=1 iff (inm[v]>>u)&1 */
        int e=0; for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(u!=v && ((inm[v]>>u)&1)){ af[e]=u; at[e]=v; e++; }
        /* e should equal C */
        for(int k=0;k<C;k++) ones[k]=1.0;
        double MASd=oracle(ones,order); long MAS=(long)(MASd+0.5);
        long MASMIN=(2*C+2)/3;                         /* ceil(2C/3) */
        double a;
        if(MAS<MASMIN) a=-1.0; else a=alpha_star(1e-9);
        printf("%ld %ld %.6f\n", idx, MAS, a);
        idx++;
    }
    free(line); fclose(fp); return 0;
}
