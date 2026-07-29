# analyze_ce1068.R — structure of the A(3) boundary counterexample allGraphs[[1068]] (regular n=11,
# alpha*=2/3, McG=5): automorphism group (by closure), circulant connection set, double-regularity,
# and the exact alpha*=2/3 dual certificate (predictability obstacle subgraph).
suppressMessages({ library(igraph); library(lpSolve); library(rcdd); library(gmp) })
source("../common/alpha_star.R")
e <- new.env(); load("../data/regulartournaments11.RData", envir = e); A <- e$allGraphs[[1068]]; n <- nrow(A)
g <- graph_from_adjacency_matrix(A, mode = "directed")
gens <- automorphism_group(g)                             # 1-based permutations

cat("=== allGraphs[[1068]] : n=11 regular tournament ===\n")
# ---- |Aut| by closing the generator set (group is small) ----
compose <- function(p, q) p[q]                            # (p∘q)[i] = p[q[i]]
id <- 1:n; grp <- list(id); key <- function(p) paste(p, collapse=",")
seen <- new.env(); assign(key(id), TRUE, seen); frontier <- list(id)
while (length(frontier)) { nf <- list()
  for (p in frontier) for (gg in gens) { r <- compose(p, gg)
    if (is.null(get0(key(r), seen))) { assign(key(r), TRUE, seen); grp[[length(grp)+1]] <- r; nf[[length(nf)+1]] <- r } }
  frontier <- nf }
cat(sprintf("|Aut| = %d  (%d generator(s))\n", length(grp), length(gens)))
for (i in seq_along(gens)) cat(sprintf("  gen %d (1-based): %s\n", i, paste(gens[[i]], collapse=" ")))
# vertex-transitive?
orbsz <- length(unique(sapply(grp, function(p) p[1])))
cat(sprintf("orbit of vertex 1 has size %d ; vertex-transitive: %s\n", orbsz, orbsz == n))
# any 11-cycle automorphism => circulant
cyc_ord <- function(p){ x<-p[1]; o<-1L; while(x!=1L && o<=n){x<-p[x]; o<-o+1L}; o }
has11 <- any(sapply(grp, function(p) cyc_ord(p) == n && length(unique(p))==n))
cat(sprintf("has an 11-cycle automorphism (=> circulant): %s\n", has11))

# ---- circulant connection set under the 11-cycle labeling ----
cyc <- grp[[ which(sapply(grp, function(p) cyc_ord(p)==n))[1] ]]   # an 11-cycle automorphism
# relabel so cyc becomes x -> x+1: order vertices along the cycle starting at 1
lab <- integer(n); v <- 1L; for (k in 1:n) { lab[k] <- v; v <- cyc[v] }   # lab[k] = k-th vertex on cycle
# connection set S = { d : arc lab[1] -> lab[1+d] } (mod n)
pos <- integer(n); pos[lab] <- 0:(n-1)
S <- sort(pos[ which(A[lab[1], ] == 1L) ])
cat(sprintf("circulant connection set S (jumps that are arcs, mod %d): {%s}\n", n, paste(S, collapse=", ")))
cat(sprintf("  (Paley(11) would be S = QR = {1,3,4,5,9}; ours differs => NOT Paley(11))\n"))

# ---- double-regularity & MAS ----
tri <- integer(0); for (u in 1:n) for (v in 1:n) if (A[u,v]==1L) tri <- c(tri, sum(A[v,]==1L & A[,u]==1L))
MAS <- maxweight_order(matrix(as.numeric(A), n, n))$value
cat(sprintf("cyclic triangles per arc in [%d,%d]; doubly-regular (all==3): %s\n", min(tri), max(tri), all(tri==3)))
cat(sprintf("MAS = %d ; MAS/C = %d/%d = %.5f  (arc-transitive iff = alpha*=2/3; here alpha*<MAS/C)\n",
            MAS, MAS, n*(n-1)/2, MAS/(n*(n-1)/2)))

# ---- alpha*=2/3 dual certificate (support subgraph = predictability obstacle) ----
a <- which(A==1L, arr.ind=TRUE); af <- a[,1]; at <- a[,2]; E <- length(af)
Wm <- function(y){ W<-matrix(0,n,n); W[cbind(af,at)]<-y; W }; con <- function(o){ p<-integer(n); p[o]<-1:n; as.numeric(p[af]<p[at]) }
cuts <- matrix(con(1:n), nrow=1)
repeat { K<-nrow(cuts); s<-lp("min",c(rep(0,E),1),rbind(c(rep(1,E),0),cbind(cuts,rep(-1,K))),c("=",rep("<=",K)),c(1,rep(0,K)))
  t<-s$solution[E+1]; y<-s$solution[1:E]; mo<-maxweight_order(Wm(y)); if(mo$value<=t+1e-9) break; cuts<-rbind(cuts,con(mo$order)) }
K<-nrow(cuts); a1<-rbind(cbind(cuts,matrix(-1,K,1)),cbind(-diag(E),matrix(0,E,1)))
ex<-lpcdd(makeH(d2q(a1),d2q(rep(0,K+E)),d2q(matrix(c(rep(1,E),0),nrow=1)),d2q(1)),d2q(c(rep(0,E),1)),minimize=TRUE)
yq <- as.bigq(ex$primal.solution[1:E]); supp <- which(yq != 0)
cat(sprintf("\nalpha*=2/3 dual certificate: %d of %d arcs carry weight; denominators {%s}\n",
            length(supp), E, paste(unique(as.character(denominator(yq[supp]))), collapse=",")))
sd <- integer(n); si <- integer(n); for (k in supp){ sd[af[k]]<-sd[af[k]]+1L; si[at[k]]<-si[at[k]]+1L }
cat("  support subgraph out-deg per vertex (0-based):", paste(sd, collapse=" "), "\n")
cat("  support subgraph  in-deg per vertex (0-based):", paste(si, collapse=" "), "\n")
saveRDS(list(A=A, S=S, lab=lab, aut=length(grp), supp_from=af[supp]-1, supp_to=at[supp]-1, mu=as.character(yq[supp])),
        "ce1068_analysis.rds")
cat("\nsaved ce1068_analysis.rds\n")
