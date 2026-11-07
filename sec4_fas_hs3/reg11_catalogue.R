# Prepares the regular n = 11 catalogue for reg11_fas_hs3.py.
#
# Reads the committed catalogue ../data/regulartournaments11.RData (object `allGraphs`,
# adjacency matrices with M[i, j] = 1 iff i -> j; McKay's list of the regular tournaments
# on 11 vertices, one per isomorphism class), and checks that every entry is a regular
# tournament and that no two entries are isomorphic (igraph canonical forms). It then
# builds T* from the three voters of tstar_voters.R and finds the one catalogue entry
# isomorphic to it.
#
# Writes <out.txt>: one bit string per entry, in catalogue order, in McKay's format
# (upper triangle row by row, bit = 1 iff i -> j for i < j), which is what
# ../appendices/margin1_scan.c and hs3fas.c read. Prints the line
#   T* = catalogue entry <k>
# with k counted from 1 in catalogue order.
#
# Usage (from this folder): Rscript reg11_catalogue.R <out.txt>
suppressPackageStartupMessages(library(igraph))
args = commandArgs(trailingOnly = TRUE)
stopifnot(length(args) == 1)
source("tstar_voters.R")   # tstar_voters, majority_matrix

e = new.env()
stopifnot(identical(load("../data/regulartournaments11.RData", envir = e), "allGraphs"))
G = e$allGraphs
n = nrow(G[[1]])

is_regular_tournament = function(M) {
  nrow(M) == n && ncol(M) == n && all(M %in% c(0, 1)) && all(diag(M) == 0) &&
    all(M + t(M) + diag(n) == 1) && all(rowSums(M) == (n - 1) / 2)
}
stopifnot(n %% 2 == 1, all(sapply(G, is_regular_tournament)))

to_bits = function(M) {
  b = character(0)
  for (i in 1:(n - 1)) for (j in (i + 1):n) b = c(b, if (M[i, j] == 1) "1" else "0")
  paste(b, collapse = "")
}

# Canonical form: relabel by igraph's canonical permutation (bliss), then read off the bits.
# Two tournaments are isomorphic iff their canonical forms are equal.
canon = function(M) {
  g = graph_from_adjacency_matrix(M, mode = "directed")
  h = permute(g, canonical_permutation(g)$labeling)
  to_bits(as.matrix(as_adjacency_matrix(h)))
}

# Control on the canonical form itself: a random relabelling of an entry must
# canonicalise to the same string (otherwise "all forms distinct" below would prove nothing).
set.seed(1)
p = sample(n)
stopifnot(identical(canon(G[[1]][p, p]), canon(G[[1]])))

cf = sapply(G, canon)
stopifnot(!anyDuplicated(cf))   # pairwise non-isomorphic
cat(length(G), "regular tournaments on", n, "vertices, pairwise non-isomorphic\n")

Tstar = majority_matrix(tstar_voters)
stopifnot(is_regular_tournament(Tstar))
hit = which(cf == canon(Tstar))
stopifnot(length(hit) == 1)     # the catalogue is complete, so T* is in it exactly once
cat("T* = catalogue entry", hit, "\n")

writeLines(sapply(G, to_bits), args[1])
