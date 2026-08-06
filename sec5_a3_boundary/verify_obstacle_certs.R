# SOLVER-FREE static certification of alpha*=(2t-1)/(3t-1) for every n=9 obstacle.
# Depends on gmp ONLY (exact rationals) -- no LP solver, no cddlib, no CPLEX in the trust path.
# Each certificate carries a primal distribution x over orders (=> alpha* >= p/q) and a dual arc-
# weighting y (=> alpha* <= p/q, checked by exact Held-Karp weighted-MAS); together alpha* = p/q.
suppressMessages(library(gmp))
# progress on stderr only (base R; not part of the certification) — see common/progress.R
if (file.exists("../common/progress.R")) source("../common/progress.R") else
  { progress <- function(...) invisible(); progress_done <- function() invisible() }
CERTS <- commandArgs(trailingOnly=TRUE)[1]; C <- readRDS(CERTS)
wmas <- function(af,at,y,n){ inv<-vector("list",n); for(k in seq_along(af)) inv[[at[k]]]<-c(inv[[at[k]]],k)
  pw<-as.integer(2^(0:(n-1))); g<-as.bigq(rep(0L,2^n))
  for(m in 1:(2^n-1)){b<-as.bigq(-1L); for(v in which(bitwAnd(m,pw)>0)){p<-m-pw[v];a<-as.bigq(0L)
    for(k in inv[[v]]) if(bitwAnd(p,pw[af[k]])>0) a<-a+y[k]; val<-g[p+1]+a; if(val>b)b<-val}; g[m+1]<-b}; g[2^n] }
ok<-0; ncert<-length(C); icert<-0L
for(cc in C){ icert<-icert+1L; progress(icert, ncert, "obstacles certified (exact Held-Karp per obstacle)")
  pq<-as.bigq(cc$alpha); x<-as.bigq(cc$x); y<-as.bigq(cc$y); E<-length(cc$af); cuts<-cc$cuts
  P  <- (sum(x)==1L) && all(x>=0) && all(sapply(1:E, function(e) sum(x[cuts[,e]==1])>=pq))   # alpha* >= p/q
  Dl <- (sum(y)==1L) && all(y>=0) && (wmas(cc$af,cc$at,y,cc$n) <= pq)                          # alpha* <= p/q
  den<-as.integer(denominator(pq)); t<-(den+1)/3
  fam<- (t==round(t)) && (pq==as.bigq(2L*as.integer(t)-1L, 3L*as.integer(t)-1L))
  if(P&&Dl&&fam) ok<-ok+1 else { progress_done(); cat(sprintf("  FAIL idx=%d %s  primal=%s dual=%s family=%s\n",cc$idx,cc$alpha,P,Dl,fam)) }
}
progress_done()
cat(sprintf("STATIC (gmp-only) certification: %d/%d obstacles, alpha*=(2t-1)/(3t-1) via primal+dual\n", ok, length(C)))
