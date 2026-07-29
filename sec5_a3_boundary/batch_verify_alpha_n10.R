# batch_verify_alpha_n10.R INMFILE GIDXFILE OUTFILE — EXACT confirmation that each n=10 tournament has
# alpha*=2/3. Method (same as verify_ce1068.R): float cutting-plane gathers cut-orders, then rcdd solves
# the dual LP over those cuts in EXACT rational arithmetic -> astar. Since {cuts} subset of all orders,
# astar = min_y max_{O in cuts} agree(O,y) <= alpha*, and alpha*<=2/3 automatically (non-transitive => a
# 3-cycle dual). So  astar == 2/3 exactly  PROVES  alpha* = 2/3.  Output: "gidx astar is23".
suppressMessages({ library(lpSolve); library(rcdd); library(gmp) })
source("../common/alpha_star.R")
args <- commandArgs(trailingOnly=TRUE); INM<-args[1]; GID<-args[2]; OUT<-args[3]; n<-10
inm_lines <- readLines(INM); gidx <- readLines(GID)
two3 <- as.bigq(2L,3L)

verify1 <- function(inm){
  A <- matrix(0L,n,n)
  for(v in 1:n){ for(u in 1:n) if(u!=v && bitwAnd(inm[v], bitwShiftL(1L,u-1L))!=0L) A[u,v]<-1L }
  a <- which(A==1L, arr.ind=TRUE); af<-a[,1]; at<-a[,2]; E<-length(af)
  Wm <- function(y){ W<-matrix(0,n,n); W[cbind(af,at)]<-y; W }
  con <- function(o){ p<-integer(n); p[o]<-1:n; as.numeric(p[af]<p[at]) }
  cuts <- matrix(con(1:n), nrow=1)
  repeat {
    K<-nrow(cuts)
    s<-lp("min", c(rep(0,E),1), rbind(c(rep(1,E),0), cbind(cuts, rep(-1,K))),
          c("=", rep("<=",K)), c(1, rep(0,K)))
    t<-s$solution[E+1]; y<-s$solution[1:E]
    mo<-maxweight_order(Wm(y))
    if(mo$value <= t+1e-9) break
    cuts<-rbind(cuts, con(mo$order))
  }
  K<-nrow(cuts); a1<-rbind(cbind(cuts,matrix(-1,K,1)), cbind(-diag(E),matrix(0,E,1)))
  hrep<-makeH(d2q(a1), d2q(rep(0,K+E)), d2q(matrix(c(rep(1,E),0),nrow=1)), d2q(1))
  ex<-lpcdd(hrep, d2q(c(rep(0,E),1)), minimize=TRUE)
  astar<-ex$optimal.value
  list(astar=as.character(astar), is23=(as.bigq(astar)==two3))
}

con_out <- file(OUT,"w")
n23<-0; nno<-0
for(i in seq_along(inm_lines)){
  inm <- as.integer(strsplit(inm_lines[i]," ")[[1]])
  r <- verify1(inm)
  if(r$is23) n23<-n23+1 else nno<-nno+1
  writeLines(sprintf("%s %s %s", gidx[i], r$astar, r$is23), con_out)
}
close(con_out)
cat(sprintf("DONE %s: alpha*=2/3 exactly: %d ; other: %d (of %d)\n", INM, n23, nno, length(inm_lines)))
