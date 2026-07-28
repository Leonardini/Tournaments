# Generate the figures for obstacle collections A' (26) and B' (25) of the manuscript
# (Tournaments_3_and_5_voters.md, Section 6), in the consistent layout of
# ObsoleteSourceFiles/Plots.R (layout_with_kk), for reproducibility.
#
# Data: Counterexamples/Non3RealisabilitySummary.RData
#   firstSampledMin  = A' (26 obstacles; minimum set cover of the 42-obstacle collection A)
#   firstCounterMin  = B' (25 obstacles; minimum set cover of the margin-1 collection B)
# NOTE: the stored pre-cover collection firstCounter has 57 entries where the draft text
# says 54 distinct — reconcile before publication (dedup up to isomorphism?).
#
# Output: Manuscript/figures/A_prime_XX.pdf, B_prime_XX.pdf and the combined grids
#   collectionA_prime.pdf, collectionB_prime.pdf.
# Run from the repository root:  Rscript Manuscript/figures/make_AB_obstacle_figures.R

library(igraph)

makeIgraphLayout = function(G) {          # Plots.R technology
  layout <- layout_with_kk(G)
  return(layout)
}

plotObstacle = function(G, fname) {
  set.seed(1)                              # deterministic layout for reproducibility
  layout = makeIgraphLayout(G)
  pdf(file = fname)
  plot(G, layout = layout, edge.color = "grey30", vertex.color = "orange",
       vertex.size = 18, edge.arrow.size = 0.5)
  dev.off()
  layout
}

plotGrid = function(graphs, fname, ncol = 5) {
  n = length(graphs)
  nrow = ceiling(n / ncol)
  pdf(file = fname, width = 3 * ncol, height = 3 * nrow)
  par(mfrow = c(nrow, ncol), mar = c(0.5, 0.5, 1.5, 0.5))
  for (i in seq_along(graphs)) {
    set.seed(1)
    layout = makeIgraphLayout(graphs[[i]])
    plot(graphs[[i]], layout = layout, edge.color = "grey30", vertex.color = "orange",
         vertex.size = 22, edge.arrow.size = 0.4, vertex.label.cex = 0.8,
         main = sprintf("%d", i))
  }
  dev.off()
}

e = new.env()
load("Counterexamples/Non3RealisabilitySummary.RData", envir = e)
output = get("output", envir = e)

Aprime = output$firstSampledMin
Bprime = output$firstCounterMin
stopifnot(length(Aprime) == 26, length(Bprime) == 25)

for (i in seq_along(Aprime)) plotObstacle(Aprime[[i]], sprintf("Manuscript/figures/A_prime_%02d.pdf", i))
for (i in seq_along(Bprime)) plotObstacle(Bprime[[i]], sprintf("Manuscript/figures/B_prime_%02d.pdf", i))
plotGrid(Aprime, "Manuscript/figures/collectionA_prime.pdf")
plotGrid(Bprime, "Manuscript/figures/collectionB_prime.pdf")
cat("Done: 26 A' + 25 B' figures + 2 grids in Manuscript/figures/\n")
