#!/usr/bin/env Rscript
# Containment matrix M[i,j] = 1 iff distinct obstacle j is a (non-induced) sub-digraph of tournament
# T_i (igraph vf2 monomorphism), over the 254 margin-1-only n=9 tournaments x 72 obstacle classes.
# Then minimum set cover ILP:  min sum_j z_j  s.t.  sum_j M[i,j] z_j >= 1  for all i,  z in {0,1}.
# Every tournament trivially contains its own obstacle(s), so a cover exists; CPLEX gives the optimum.
suppressMessages({ library(igraph); library(Rcplex) })
DATA <- Sys.getenv("NM1_DATA", "../data")
args <- commandArgs(trailingOnly = TRUE)
CAT    <- if (length(args) >= 1) args[1] else file.path(DATA, "n9_nm1_obstacle_catalog.rds")
OUTRDS <- if (length(args) >= 2) args[2] else file.path(DATA, "n9_nm1_obstacle_cover.rds")

CE <- readRDS(file.path(DATA, "n9_margin1only_tournaments.rds"))     # 254 adjacency matrices
distinct <- readRDS(CAT)$distinct; Nd <- length(distinct)
cat(sprintf("tournaments: %d ; distinct obstacle classes: %d\n", length(CE), Nd)); flush.console()

PAT <- lapply(distinct, function(o) graph_from_adjacency_matrix(o$D, mode = "directed"))
TG  <- lapply(CE, function(A) graph_from_adjacency_matrix(A, mode = "directed"))
Nt  <- length(CE)

M <- matrix(0L, Nt, Nd)
for (j in seq_len(Nd)) { pj <- PAT[[j]]
  for (i in seq_len(Nt)) if (subgraph_isomorphic(pj, TG[[i]], method = "vf2")) M[i, j] <- 1L
  if (j %% 20 == 0) { cat(sprintf("  containment col %d/%d\n", j, Nd)); flush.console() } }
rs <- rowSums(M)
cat(sprintf("M %d x %d, density %.3f; every tournament covered by >=1 class: %s\n", Nt, Nd, mean(M), all(rs >= 1)))
stopifnot(all(rs >= 1))

sol <- Rcplex(cvec = rep(1, Nd), Amat = matrix(as.double(M), nrow = Nt), bvec = rep(1, Nt),
              sense = rep("G", Nt), vtype = rep("B", Nd), lb = rep(0, Nd), ub = rep(1, Nd),
              objsense = "min", control = list(trace = 0, epgap = 0))
suppressMessages(Rcplex.close())
sel <- which(sol$xopt > 0.5)
stopifnot(all(rowSums(M[, sel, drop = FALSE]) >= 1))
cat(sprintf("\n== MINIMUM SET COVER: %d classes (CPLEX status %s, optimal) covering all %d tournaments ==\n",
            length(sel), sol$status, Nt))
cat(" selected classes:", paste(sel, collapse = " "), "\n")
cat(" their alpha^= values:", paste(sapply(distinct[sel], function(o) o$alpha), collapse = " "), "\n")
saveRDS(list(distinct = distinct, M = M, selected = sel, cover_size = length(sel), row_sums = rs), OUTRDS)
cat(sprintf("saved %s\n", OUTRDS))
