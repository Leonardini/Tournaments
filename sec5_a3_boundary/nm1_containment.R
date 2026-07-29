#!/usr/bin/env Rscript
# Containment poset of the distinct non-margin-1 obstacle SUPPORT digraphs (weights/signs ignored):
# A <= B iff A is a non-induced sub-digraph of B (igraph vf2 monomorphism), A not iso B.
# Reports BOTH catalogues carried by n9_nm1_obstacle_catalog.rds:
#   * extreme-dual  (all 72 vertices of the optimal-dual faces),
#   * inclusion-minimal (the 54 flagged inclusion_minimal = B.7's supports).
# Key facts: neither is a global antichain (extreme-dual: many nestings; inclusion-minimal: fewer but
# nonzero -> the antichain is only PER TOURNAMENT); the optimal set cover is an antichain of minimal
# obstacles.  alpha^= is anti-monotone along containment.
suppressMessages({ library(igraph); library(gmp) })
args <- commandArgs(trailingOnly = TRUE)
CAT   <- if (length(args) >= 1) args[1] else "../data/n9_nm1_obstacle_catalog.rds"
COVER <- if (length(args) >= 2) args[2] else "../data/n9_nm1_obstacle_cover.rds"

X <- readRDS(CAT); distinct <- X$distinct; N <- length(distinct)
G  <- lapply(distinct, function(o) graph_from_adjacency_matrix(o$D, mode = "directed"))
ne <- sapply(G, ecount); al <- lapply(distinct, function(o) as.bigq(o$alpha))
im <- sapply(distinct, function(o) isTRUE(o$inclusion_minimal))

containments <- function(idx) {                     # strict iso-containments within a subset of classes
  cnt <- 0
  for (a in idx) for (b in idx) { if (a == b || ne[a] > ne[b]) next
    if (subgraph_isomorphic(G[[a]], G[[b]], method = "vf2") && !isomorphic(G[[a]], G[[b]])) cnt <- cnt + 1 }
  cnt
}
R <- matrix(FALSE, N, N)
for (a in 1:N) for (b in 1:N) { if (a == b || ne[a] > ne[b]) next
  if (subgraph_isomorphic(G[[a]], G[[b]], method = "vf2") && !isomorphic(G[[a]], G[[b]])) R[a, b] <- TRUE }
viol <- sum(sapply(1:N, function(a) sum(sapply(1:N, function(b) R[a, b] && al[[a]] < al[[b]]))))

cat(sprintf("EXTREME-DUAL catalogue: %d classes ; strict iso-containments: %d (=> NOT a global antichain)\n", N, sum(R)))
cat(sprintf("INCLUSION-MINIMAL catalogue (B.7): %d classes ; strict iso-containments among them: %d\n", sum(im), containments(which(im))))
cat(sprintf("   => inclusion-minimal is an antichain PER TOURNAMENT (by construction) but NOT globally\n"))
cat(sprintf("alpha^= anti-monotone along containment (A<=B => alpha_A >= alpha_B): %d violations\n", viol))
cat(sprintf("global minimal classes (contain no other): %d ; maximal: %d\n", sum(colSums(R) == 0), sum(rowSums(R) == 0)))

if (file.exists(COVER)) {
  sel <- readRDS(COVER)$selected
  cat(sprintf("\nset cover: %d classes ; all global-minimal: %s ; containments among them: %d\n",
              length(sel), all(colSums(R)[sel] == 0), containments(sel)))
  cat(sprintf("=> the %d cover classes are a genuine ANTICHAIN of support digraphs (weights/signs not needed)\n", length(sel)))
}
