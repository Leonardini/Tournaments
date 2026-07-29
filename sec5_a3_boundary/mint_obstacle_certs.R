# Mint exact primal+dual certificates for the n=9 obstacle predictability values alpha*=(2t-1)/(3t-1).
# This is the ONLY solver step (rcdd exact LP + lpSolve column-gen seed + the alpha_star.R oracle);
# the certificates it writes (n9_obstacle_certs.rds) are re-checked SOLVER-FREE by
# verify_obstacle_certs.R (gmp only).  Run from this folder:  Rscript mint_obstacle_certs.R
suppressMessages({ library(lpSolve); library(rcdd); library(gmp) })
source("../common/alpha_star.R")                                     # maxweight_order (float, seeding only)
X <- readRDS("../data/n9_obstacle_catalog_exact.rds")
ewm_ord <- function(af,at,yq,n){ inv<-vector("list",n); for(k in seq_along(af)) inv[[at[k]]]<-c(inv[[at[k]]],k)
  pw<-as.integer(2^(0:(n-1))); g<-as.bigq(rep(0L,2^n)); ch<-integer(2^n)
  for(m in 1:(2^n-1)){b<-as.bigq(-1L);bv<-0L; for(v in which(bitwAnd(m,pw)>0)){p<-m-pw[v];a<-as.bigq(0L)
    for(k in inv[[v]]) if(bitwAnd(p,pw[af[k]])>0) a<-a+yq[k]; val<-g[p+1]+a; if(val>b){b<-val;bv<-v}}; g[m+1]<-b; ch[m+1]<-bv}
  mm<-2^n-1; ord<-integer(n); q<-n; while(mm>0){v<-ch[mm+1];ord[q]<-v;q<-q-1;mm<-mm-pw[v]}; list(value=g[2^n],order=ord) }
mint <- function(D){ n<-nrow(D); a<-which(D==1L,arr.ind=TRUE); af<-a[,1]; at<-a[,2]; E<-length(af)
  Wm<-function(y){W<-matrix(0,n,n);W[cbind(af,at)]<-y;W}; con<-function(o){p<-integer(n);p[o]<-1:n;as.numeric(p[af]<p[at])}
  cuts<-matrix(con(1:n),nrow=1)
  repeat{K<-nrow(cuts);s<-lp("min",c(rep(0,E),1),rbind(c(rep(1,E),0),cbind(cuts,rep(-1,K))),c("=",rep("<=",K)),c(1,rep(0,K)))
    mo<-maxweight_order(Wm(s$solution[1:E]));if(mo$value<=s$solution[E+1]+1e-9)break;cuts<-rbind(cuts,con(mo$order))}
  repeat{K<-nrow(cuts);ex<-lpcdd(makeH(d2q(rbind(cbind(cuts,matrix(-1,K,1)),cbind(-diag(E),matrix(0,E,1)))),d2q(rep(0,K+E)),d2q(matrix(c(rep(1,E),0),nrow=1)),d2q(1)),d2q(c(rep(0,E),1)),minimize=TRUE)
    yq<-as.bigq(ex$primal.solution[1:E]);mo<-ewm_ord(af,at,yq,n);if(mo$value<=as.bigq(ex$optimal.value))break;cuts<-rbind(cuts,con(mo$order))}
  Kc<-nrow(cuts); Aineq<-rbind(cbind(-diag(Kc),rep(0,Kc)),cbind(-t(cuts),rep(1,E)))
  exP<-lpcdd(makeH(d2q(Aineq),d2q(rep(0,Kc+E)),d2q(matrix(c(rep(1,Kc),0),nrow=1)),d2q(1)),d2q(c(rep(0,Kc),-1)),minimize=TRUE)
  keep<-which(as.bigq(exP$primal.solution[1:Kc])!=0)                 # store only the primal support orders
  list(af=af,at=at,n=n,cuts=cuts[keep,,drop=FALSE], x=as.character(as.bigq(exP$primal.solution[1:Kc])[keep]), y=as.character(yq)) }
C <- lapply(seq_along(X$distinct), function(i){ o<-X$distinct[[i]]; c(list(idx=o$idx, alpha=o$alpha), mint(o$D)) })
saveRDS(C, "n9_obstacle_certs.rds"); cat(sprintf("minted %d certificates -> n9_obstacle_certs.rds\n", length(C)))
