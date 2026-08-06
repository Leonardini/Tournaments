# n10_prefilter.R infile outfile offset : classify n=10 tournaments (45-bit upper-tri lines) by whether
# any of their 10 nine-vertex induced subs is a genuine non-3-realizable n=9 obstacle (=> the n=10 is
# non-3-realizable, RESOLVED). Writes 0-based global indices (offset+localline) of the UNRESOLVED ones
# (every 9-sub 3-realizable) = the A(3) counterexample candidates. Canonical form via igraph BLISS.
suppressMessages(library(igraph))
# progress on stderr only (base R) — see common/progress.R; PROGRESS=0 silences it
if (file.exists("../common/progress.R")) source("../common/progress.R") else
  { progress <- function(...) invisible(); progress_done <- function() invisible() }
a<-commandArgs(trailingOnly=TRUE); infile<-a[1]; outfile<-a[2]; offset<-as.numeric(a[3]); n<-10
keys<-readRDS("../data/n9_obstacle_keys.rds")
obs<-new.env(hash=TRUE,size=as.integer(length(keys)*1.4)); for(k in keys) assign(k,TRUE,envir=obs)
ck<-function(A){ inv<-order(canonical_permutation(graph_from_adjacency_matrix(A,mode="directed"))$labeling)
  B<-A[inv,inv]; paste(as.integer(B),collapse="") }
pu<-do.call(rbind,lapply(1:(n-1),function(i) cbind(i,(i+1):n))); pl<-pu[,c(2,1)]
lines<-readLines(infile); N<-length(lines); isun<-logical(N)
t0<-Sys.time()
for(li in seq_len(N)){
  progress(li, N, "n=10 tournaments screened")
  b<-utf8ToInt(lines[li])-48L; A<-matrix(0L,n,n); A[pu]<-b; A[pl]<-1L-b
  hit<-FALSE
  for(v in 1:n) if(!is.null(get0(ck(A[-v,-v]),envir=obs))){ hit<-TRUE; break }
  isun[li]<-!hit
}
progress_done()
writeLines(as.character(as.integer(offset)+which(isun)-1L), outfile)
dt<-as.numeric(Sys.time()-t0,units="secs")
cat(sprintf("chunk %s: N=%d resolved(non-3-real)=%d unresolved(candidates)=%d  %.1fs (%.3f ms/tourn)\n",
    infile, N, sum(!isun), sum(isun), dt, 1000*dt/N))
