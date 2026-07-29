# verify_ce1068.R — INDEPENDENT end-to-end verification of the candidate Conjecture A(3)
# counterexample: regular n=11 tournament allGraphs[[1068]], claimed alpha*=2/3 & not 3-realizable.
# Recomputes everything from the raw tournament (no cross-file index alignment) to rule out off-by-one.
suppressMessages({ library(lpSolve); library(rcdd); library(gmp) })
source("../common/alpha_star.R")
IDX <- 1068
e <- new.env(); load("../data/regulartournaments11.RData", envir = e); A <- e$allGraphs[[IDX]]
n <- nrow(A)
cat(sprintf("=== allGraphs[[%d]] : n=%d ===\n", IDX, n))
cat("out-degrees:", paste(rowSums(A), collapse=" "), " (regular iff all 5)\n")
cat("valid tournament:", all((A + t(A))[upper.tri(A)] == 1) && all(diag(A) == 0), "\n")

# ---- exact alpha* with rational certificate (general oracle) ----
a <- which(A == 1L, arr.ind = TRUE); af <- a[,1]; at <- a[,2]; E <- length(af)
Wm <- function(y){ W <- matrix(0,n,n); W[cbind(af,at)] <- y; W }
con <- function(o){ p <- integer(n); p[o] <- 1:n; as.numeric(p[af] < p[at]) }
cuts <- matrix(con(1:n), nrow=1)
repeat { K<-nrow(cuts); s<-lp("min",c(rep(0,E),1),rbind(c(rep(1,E),0),cbind(cuts,rep(-1,K))),
    c("=",rep("<=",K)),c(1,rep(0,K))); t<-s$solution[E+1]; y<-s$solution[1:E]
  mo<-maxweight_order(Wm(y)); if(mo$value<=t+1e-9) break; cuts<-rbind(cuts,con(mo$order)) }
K<-nrow(cuts); a1<-rbind(cbind(cuts,matrix(-1,K,1)),cbind(-diag(E),matrix(0,E,1)))
hrep<-makeH(d2q(a1),d2q(rep(0,K+E)),d2q(matrix(c(rep(1,E),0),nrow=1)),d2q(1))
ex<-lpcdd(hrep,d2q(c(rep(0,E),1)),minimize=TRUE)
yq<-ex$primal.solution[1:E]; astar<-ex$optimal.value
# certify: at the exact optimum weighting, NO order beats alpha* (oracle re-check, exact-rational value)
W<-matrix(0,n,n); W[cbind(af,at)]<-q2d(yq); mo<-maxweight_order(W)
cat(sprintf("\nalpha* = %s (%.10f)   [rcdd status %s]\n", as.character(astar), q2d(astar), ex$solution.type))
cat(sprintf("certificate re-check: best order weight %.10f <= alpha*+1e-9 ? %s (gap %.2e)\n",
            mo$value, mo$value <= q2d(astar)+1e-9, mo$value - q2d(astar)))
cat(sprintf("alpha* == 2/3 exactly ? %s\n", as.bigq(astar) == as.bigq(2L,3L)))

# ---- emit inmasks for the ILP realizability check (arc u->v => bit u set in inm[v]) ----
inm <- sapply(1:n, function(v) sum(ifelse(A[,v]==1L, bitwShiftL(1L,(1:n)-1L), 0L)))
writeLines(paste(inm, collapse=" "), "ce1068_inmask.txt")
cat("\nwrote ce1068_inmask.txt (single tournament, for realize_k.py)\n")
cat("adjacency (row i, arc i->j where 1):\n"); for(i in 1:n) cat(" ", paste(A[i,],collapse=""), "\n")
