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

source("tstar_voters.R")   # tstar_voters, majority_matrix
n = 11
M = majority_matrix(tstar_voters)
stopifnot(nrow(M) == n)
edges = NULL
for (i in 1:(n - 1)) for (j in (i + 1):n) {
  edges = rbind(edges, if (M[i, j] == 1) c(i, j) else c(j, i))
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

# shared layout. The two orbits {4,5,6} and {8,9,10} are cyclic triangles and modules (every
# other vertex beats all three or none of each; checked below), so each is drawn as a small
# triangle of its own. The five other vertices and the two triangles sit on a circle in the
# witness order, clockwise from the top, so the FAS panel's backward arcs read against it.
blocks = list(c(4, 5, 6), c(8, 9, 10))
for (B in blocks) {
  stopifnot(adj[B[1], B[2]], adj[B[2], B[3]], adj[B[3], B[1]])          # a cyclic triangle
  for (x in setdiff(1:n, B)) stopifnot(length(unique(adj[x, B])) == 1)  # a module
}
slots = list()
for (v in worder) {
  B = Filter(function(B) v %in% B, blocks)
  if (length(B) == 0) slots[[length(slots) + 1]] = v
  else if (v == B[[1]][1]) slots[[length(slots) + 1]] = B[[1]]
}
stopifnot(length(slots) == n - 2 * length(blocks))
lay = matrix(0, n, 2)
rBlock = 0.15
for (i in seq_along(slots)) {
  ang = pi / 2 - 2 * pi * (i - 1) / length(slots)
  centre = c(cos(ang), sin(ang))
  S = slots[[i]]
  if (length(S) == 1) lay[S, ] = centre
  else for (t in 1:3) {
    a = ang + 2 * pi * (t - 1) / 3
    lay[S[t], ] = centre + rBlock * c(cos(a), sin(a))
  }
}

drawPanel = function(hi, hiCol, fname) {
  ecol = rep("gray70", nrow(edges)); ecol[hi] = hiCol
  ewid = rep(1.2, nrow(edges));      ewid[hi] = 3
  pdf(fname, width = 6, height = 6)
  par(mar = c(0.2, 0.2, 0.2, 0.2))
  plot.new(); plot.window(xlim = c(-1.2, 1.2), ylim = c(-1.1, 1.3), asp = 1)
  for (B in blocks) {   # a shaded disc behind each triangle module
    cx = mean(lay[B, 1]); cy = mean(lay[B, 2]); th = seq(0, 2 * pi, length.out = 100)
    polygon(cx + 0.25 * cos(th), cy + 0.25 * sin(th), col = "#EFE6D2", border = "#C9B58A")
  }
  plot(g, layout = lay, rescale = FALSE, add = TRUE,
       vertex.color = "orange", vertex.label = 1:n, vertex.label.cex = 0.85,
       vertex.label.color = "navy", vertex.size = 11,
       edge.color = ecol, edge.width = ewid,
       edge.arrow.size = 0.35, edge.curved = 0.05)
  dev.off()
  cat(fname, "written\n")
}

drawPanel(hsIdx, "blue", "Tstar_HS.pdf")
drawPanel(backIdx, "red", "Tstar_FAS.pdf")
