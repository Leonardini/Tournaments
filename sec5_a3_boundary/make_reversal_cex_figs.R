# Figures for the four n=10 forced-arc reversal counterexamples (manuscript S5,
# Theorem 5.5).  Vertices labelled 1-10 (manuscript convention); the forced arc
# (whose reversal remains 3-inducible) is drawn thick black.  The u/v fields
# below are 0-based (code convention); labels shown are u+1 -> v+1.
library(igraph)
# outputs are written to the working directory -- run this script from its own folder

cases <- list(
  list(name = "ReversalCEX_A", u = 3, v = 7,
       bits = "110110110110011111110101111111111011010111111"),
  list(name = "ReversalCEX_B", u = 0, v = 7,
       bits = "110110111110011111111110110101111011010111111"),
  list(name = "ReversalCEX_C", u = 3, v = 9,
       bits = "101001111111101011111011111111101011110110111"),
  list(name = "ReversalCEX_D", u = 3, v = 9,
       bits = "101011011111001111111101111111110101101110111"))

n <- 10
pairs <- do.call(rbind, unlist(lapply(1:(n - 1), function(i)
  lapply((i + 1):n, function(j) c(i, j))), recursive = FALSE))

for (cs in cases) {
  bits <- strsplit(cs$bits, "")[[1]]
  stopifnot(length(bits) == nrow(pairs))
  edges <- t(sapply(seq_len(nrow(pairs)), function(k) {
    i <- pairs[k, 1]; j <- pairs[k, 2]
    if (bits[k] == "1") c(i, j) else c(j, i)   # 1-indexed vertices i,j
  }))
  g <- graph_from_edgelist(edges, directed = TRUE)
  forced <- which(edges[, 1] == cs$u + 1 & edges[, 2] == cs$v + 1)
  stopifnot(length(forced) == 1)
  ecol <- rep("gray70", ecount(g)); ecol[forced] <- "black"
  ewid <- rep(1, ecount(g));        ewid[forced] <- 3.5
  pdf(paste0(cs$name, ".pdf"), width = 6, height = 6)
  par(mar = c(0.5, 0.5, 0.5, 0.5))
  plot(g, layout = layout_in_circle(g),
       vertex.color = "orange", vertex.label = 1:n,
       vertex.label.color = "navy", vertex.size = 18,
       edge.color = ecol, edge.width = ewid,
       edge.arrow.size = 0.45, edge.curved = 0.08)
  dev.off()
  cat(cs$name, "written; forced arc", cs$u, "->", cs$v, "\n")
}
