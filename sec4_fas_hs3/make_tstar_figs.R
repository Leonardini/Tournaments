# Regenerates the T* figures (manuscript Counterexample 4.2 / Figure 3) with the
# CURRENT manuscript labeling and FAS witness order (4,5,6,11,8,9,10,1,2,3,7) --
# the old graph_with_HS/graph_with_FAS predate a relabeling.  Both panels share
# one layout: the vertices on a circle in the witness order, clockwise from the
# top, so the FAS panel's backward arcs read directly against the order.
# All claims are re-verified here: T* is regular, the witness order leaves
# exactly 17 arcs backward, and the minimum 3-cycle hitting set has size 16
# (solved exactly with lpSolve).
library(igraph)
library(lpSolve)
# outputs are written to the working directory -- run this script from its own folder

voters = list(c(4, 5, 6, 11, 8, 9, 10, 2, 7, 1, 3),
              c(9, 1, 2, 3, 7, 5, 6, 4, 11, 10, 8),
              c(10, 8, 3, 7, 11, 1, 2, 6, 4, 5, 9))
n = 11
L = matrix(0, n, n)
for (v in voters) for (a in 1:(n - 1)) for (b in (a + 1):n) {
  L[v[a], v[b]] = L[v[a], v[b]] + 1
}
edges = NULL
for (i in 1:(n - 1)) for (j in (i + 1):n) {
  stopifnot(L[i, j] != L[j, i])
  edges = rbind(edges, if (L[i, j] > L[j, i]) c(i, j) else c(j, i))
}
g = graph_from_edgelist(edges, directed = TRUE)
stopifnot(all(degree(g, mode = "out") == 5))  # T* is regular

# FAS: backward set of the witness order
worder = c(4, 5, 6, 11, 8, 9, 10, 1, 2, 3, 7)
pos = match(1:n, worder)
backIdx = which(pos[edges[, 1]] > pos[edges[, 2]])
stopifnot(length(backIdx) == 17)
cat("FAS check: witness order leaves", length(backIdx), "arcs backward\n")

# minimum 3-cycle hitting set, exact (lpSolve, binary)
adj = matrix(FALSE, n, n); adj[edges] = TRUE
rows = NULL
for (i in 1:(n - 2)) for (j in (i + 1):(n - 1)) for (k in (j + 1):n) {
  tri = c(i, j, k)
  sub = adj[tri, tri]
  if (all(rowSums(sub) == 1)) {  # cyclic triangle: each vertex beats exactly one
    row = rep(0, nrow(edges))
    for (a in 1:3) for (b in 1:3) if (sub[a, b]) {
      row[which(edges[, 1] == tri[a] & edges[, 2] == tri[b])] = 1
    }
    rows = rbind(rows, row)
  }
}
cat("cyclic triangles:", nrow(rows), "\n")
sol = lp("min", rep(1, nrow(edges)), rows, rep(">=", nrow(rows)),
         rep(1, nrow(rows)), all.bin = TRUE)
stopifnot(sol$status == 0, abs(sol$objval - 16) < 1e-9)
hsIdx = which(sol$solution > 0.5)
cat("HS check: minimum 3-cycle hitting set has", length(hsIdx), "arcs\n")

# shared layout: circle in witness order, clockwise from the top
lay = matrix(0, n, 2)
for (i in 1:n) {
  ang = pi / 2 - 2 * pi * (i - 1) / n
  lay[worder[i], ] = c(cos(ang), sin(ang))
}

drawPanel = function(hi, hiCol, fname) {
  ecol = rep("gray70", nrow(edges)); ecol[hi] = hiCol
  ewid = rep(1.2, nrow(edges));      ewid[hi] = 3
  pdf(fname, width = 6, height = 6)
  par(mar = c(0.5, 0.5, 0.5, 0.5))
  plot(g, layout = lay,
       vertex.color = "orange", vertex.label = 1:n,
       vertex.label.color = "navy", vertex.size = 16,
       edge.color = ecol, edge.width = ewid,
       edge.arrow.size = 0.4, edge.curved = 0.08)
  dev.off()
  cat(fname, "written\n")
}

drawPanel(hsIdx, "blue", "Tstar_HS.pdf")
drawPanel(backIdx, "red", "Tstar_FAS.pdf")
