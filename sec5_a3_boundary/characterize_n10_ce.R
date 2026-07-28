# characterize_n10_ce.R INMFILE — structural profile of the n=10 A(3) counterexamples (non-3-real, alpha*=2/3).
# Reports |Aut| distribution (rigid vs symmetric), confirms none are regular, out-degree-sequence variety,
# and full detail of the first (smallest catalogue index) as a canonical representative.
suppressMessages(library(igraph))
INM <- commandArgs(trailingOnly=TRUE)[1]; n <- 10
lines <- readLines(INM)
build <- function(inm){ A<-matrix(0L,n,n); for(v in 1:n) for(u in 1:n) if(u!=v && bitwAnd(inm[v],bitwShiftL(1L,u-1L))!=0L) A[u,v]<-1L; A }
mas <- function(A){ # exact MAS via DP over subsets (n=10)
  best<-integer(2^n); # best[S]=max forward arcs within vertex set S ordered optimally (Held-Karp style)
  # f[S] = max over last vertex v in S of f[S\v] + (#arcs from S\v into v)
  f<-integer(2^n); f[1]<-0
  for(S in 1:(2^n-1)){ mx<--1
    for(v in 0:(n-1)) if(bitwAnd(S,bitwShiftL(1L,v))!=0L){ P<-bitwXor(S,bitwShiftL(1L,v))
      add<-0L; for(u in 0:(n-1)) if(bitwAnd(P,bitwShiftL(1L,u))!=0L && A[u+1,v+1]==1L) add<-add+1L
      cand<-f[P+1]+add; if(cand>mx) mx<-cand }
    f[S+1]<-mx }
  f[2^n] }
auts<-integer(length(lines)); reg<-logical(length(lines)); selfc<-logical(length(lines)); degseqs<-character(length(lines))
for(i in seq_along(lines)){ inm<-as.integer(strsplit(lines[i]," ")[[1]]); A<-build(inm)
  g<-graph_from_adjacency_matrix(A,mode="directed")
  auts[i]<-count_automorphisms(g)$group_size %in% c() # placeholder
}
# count_automorphisms returns different structure across igraph versions; use automorphism_group length product
autsize<-function(A){ g<-graph_from_adjacency_matrix(A,mode="directed"); ag<-automorphism_group(g); if(length(ag)==0) 1 else { # order = product? use count
  ca<-tryCatch(count_automorphisms(g), error=function(e) NULL); if(!is.null(ca)) as.numeric(ca$group_size) else length(ag) } }
for(i in seq_along(lines)){ inm<-as.integer(strsplit(lines[i]," ")[[1]]); A<-build(inm)
  auts[i]<-autsize(A); od<-rowSums(A); reg[i]<-all(od==od[1]); degseqs[i]<-paste(sort(od),collapse="")
  # self-converse: exists permutation making A == t(A) up to iso  <=> g iso to reverse(g)
  g<-graph_from_adjacency_matrix(A,mode="directed"); gr<-graph_from_adjacency_matrix(t(A),mode="directed")
  selfc[i]<-igraph::isomorphic(g,gr)
}
cat(sprintf("n=10 A(3) counterexamples: %d\n", length(lines)))
cat("|Aut| distribution:\n"); print(table(auts))
cat(sprintf("regular (out-deg all equal): %d (expected 0 - no regular tournaments at even n)\n", sum(reg)))
cat(sprintf("self-converse: %d / %d\n", sum(selfc), length(lines)))
cat(sprintf("distinct out-degree sequences: %d\n", length(unique(degseqs))))
# canonical smallest example
inm1<-as.integer(strsplit(lines[1]," ")[[1]]); A1<-build(inm1)
cat("\n=== canonical example (first) ===\n")
cat("inmask:", paste(inm1,collapse=" "), "\n")
cat("out-degrees:", paste(rowSums(A1),collapse=" "), "\n")
cat(sprintf("|Aut|=%s  self-converse=%s  MAS=%d (MAS/C=%d/45=%.3f)\n", format(auts[1]), selfc[1], mas(A1), mas(A1), mas(A1)/45))
cat("adjacency (row i: arc i->j where 1):\n"); for(i in 1:n) cat("  ", paste(A1[i,],collapse=""), "\n")
