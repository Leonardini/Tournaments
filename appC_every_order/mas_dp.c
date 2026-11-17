/* mas_dp.c — exact MAS of arbitrary tournaments (n<=27) by Held-Karp subset DP.
 * Generalizes mas31.c: reads per-vertex in-masks instead of building them from QRs.
 *   f[S] = max #forward arcs of a linear order of S = max_{v in S} f[S\v] + |in(v) & S|
 *   (v placed last among S). int16 suffices (MAS <= C(27,2)=351). Table = 2^n * 2 bytes.
 * For n=27 that is 256 MB; the table is allocated ONCE and reused across all tournaments
 * in the requested slice (so one worker = one 256 MB footprint).
 *
 * Input file: one tournament per line, n space-separated uint32 in-masks.
 *   inmask[v] = bitset of u with arc u->v (bit u = 1<<u).
 * Usage: ./mas_dp inmasks.txt n lo hi   (process tournaments [lo,hi), 0-based)
 * Output (stdout): "idx MAS minFAS" per tournament.  C = n*(n-1)/2.
 *
 * n = 28..34 (added 2026-11-16, for FAS(C3[T*,T*,T*]) at n = 33): the same recursion on min FAS instead,
 *   g[S] = min_{v in S} g[S\v] + |out(v) & S|   (v last: its arcs into S are backward),
 * in a uint8 table (2^n bytes: 8 GiB at n = 33).  g is monotone under taking subsets, so every entry is
 * <= g[FULL]; the run aborts if any entry would exceed 254.  n <= 27 takes the original int16 path unchanged.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char** argv){
  if(argc < 5){ fprintf(stderr,"usage: %s inmasks.txt n lo hi\n", argv[0]); return 1; }
  const char* path = argv[1];
  int n = atoi(argv[2]);
  int lo = atoi(argv[3]);
  int hi = atoi(argv[4]);
  if(n < 3 || n > 34){ fprintf(stderr,"n out of range (3..34)\n"); return 1; }

  /* read all tournaments' in-masks */
  FILE* fp = fopen(path,"r");
  if(!fp){ fprintf(stderr,"cannot open %s\n", path); return 1; }
  int cap = 1024, cnt = 0;
  uint64_t (*masks)[64] = malloc((size_t)cap * sizeof(*masks));
  char* line = NULL; size_t lcap = 0;
  while(getline(&line, &lcap, fp) != -1){
    if(line[0]=='\n' || line[0]=='\0') continue;
    if(cnt == cap){ cap *= 2; masks = realloc(masks, (size_t)cap*sizeof(*masks)); }
    char* p = line;
    for(int v=0; v<n; v++){
      masks[cnt][v] = (uint64_t)strtoull(p, &p, 10);
    }
    cnt++;
  }
  fclose(fp);
  free(line);
  if(lo < 0) lo = 0;
  if(hi > cnt) hi = cnt;

  uint64_t FULL = ((uint64_t)1<<n) - 1;
  int C = n*(n-1)/2;
  if(n > 27){
    uint8_t* g = malloc(FULL+1);
    if(!g){ fprintf(stderr,"malloc failed (%.2f GB)\n",(FULL+1)/1073741824.0); return 1; }
    for(int idx=lo; idx<hi; idx++){
      uint64_t outm[64] = {0};
      for(int v=0; v<n; v++) for(int u=0; u<n; u++) if(masks[idx][u] >> v & 1) outm[v] |= (uint64_t)1<<u;
      g[0]=0;
      for(uint64_t S=1; S<=FULL; S++){
        int best = 1<<30; uint64_t T = S;
        while(T){
          int v = __builtin_ctzll(T); T &= T-1;
          int val = g[S ^ ((uint64_t)1<<v)] + __builtin_popcountll(outm[v] & S);
          if(val < best) best = val;
        }
        if(best > 254){ fprintf(stderr,"uint8 overflow at S=%llu\n",(unsigned long long)S); return 2; }
        g[S] = (uint8_t)best;
        if((S & ((1ULL<<30)-1)) == 0){ fprintf(stderr,"progress %llu/%llu\n",(unsigned long long)(S>>30),(unsigned long long)((FULL+1)>>30)); }
      }
      int FAS = g[FULL];
      printf("%d %d %d\n", idx, C-FAS, FAS);
      fflush(stdout);
    }
    free(g); free(masks);
    return 0;
  }
  int16_t* f = malloc((FULL+1)*sizeof(int16_t));
  if(!f){ fprintf(stderr,"malloc failed (%.2f GB)\n",(FULL+1)*2.0/1073741824.0); return 1; }

  for(int idx=lo; idx<hi; idx++){
    uint32_t inm[32]; for(int v=0; v<n; v++) inm[v] = (uint32_t)masks[idx][v];
    f[0]=0;
    for(uint64_t S=1; S<=FULL; S++){
      int best = -1;
      uint32_t T = (uint32_t)S;
      while(T){
        int v = __builtin_ctz(T); T &= T-1;
        int val = f[S ^ (1u<<v)] + __builtin_popcount(inm[v] & (uint32_t)S);
        if(val > best) best = val;
      }
      f[S] = (int16_t)best;
    }
    int MAS = f[FULL];
    printf("%d %d %d\n", idx, MAS, C-MAS);
    fflush(stdout);
  }
  free(f); free(masks);
  return 0;
}
