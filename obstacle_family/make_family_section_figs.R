# Figure fig:family of paper 1 (Section sec:family): the obstacles G_10 and H_11, coloured by the
# arc classes the section defines -- arcs of the zigzag path, arcs at the two hubs, the defect
# 4-cycle, and the other arcs.  Same vertex/arc lists as make_family_and_mhp_figs.R; Kamada-Kawai
# layouts from seeded random starts (seeds 43 and 134), chosen so that no arc passes through a
# vertex other than its ends.  Writes into the directory it is run from.  The arc counts, the
# Eulerian property, the class sizes and that clearance are checked before plotting.
library(igraph)

familyG = function(k) {  # G_n, n = 6 + 2k
  U = paste0("U", 1:k); W = paste0("W", 1:k)
  rbind(
    data.frame(from = "T0", to = c("T1", "T2", "T3"), class = "core"),
    data.frame(from = c("T1", "T2"), to = "T3", class = "core"),
    data.frame(from = c("T3", "P1", "T3", "P2"), to = c("P1", "T0", "P2", "T0"), class = "port"),
    data.frame(from = c("T1", "P2", "T2", "P1"), to = c("P2", "T2", "P1", "T1"), class = "defect"),
    data.frame(from = rep(c("T1", "T2"), each = k), to = rep(U, 2), class = "block"),
    data.frame(from = rep(W, 2), to = rep(c("T1", "T2"), each = k), class = "block"),
    data.frame(from = "U1", to = "W1", class = "zigzag"),
    if (k >= 2) data.frame(from = rep(paste0("U", 2:k), 2),
                           to = c(paste0("W", 1:(k - 1)), paste0("W", 2:k)), class = "zigzag") else NULL,
    data.frame(from = c("U1", "T3"), to = c("T0", W[k]), class = "terminal"))
}
familyH = function(k) {  # H_n, n = 9 + 2k, k >= 1
  U = paste0("U", 1:k); W = paste0("W", 1:k)
  rbind(
    data.frame(from = c("N0", "N0", "N1", "N1", "N2"), to = c("N2", "N3", "N2", "N3", "N3"), class = "core"),
    data.frame(from = c("N2", "N2", "P2"), to = c("P1", "P2", "G"), class = "port"),
    data.frame(from = c("N0", "P2", "N1", "P1"), to = c("P2", "N1", "P1", "N0"), class = "defect"),
    data.frame(from = c("N2", "N3", "F", "F", "N3", "G", "G", "N3", "H", "H"),
               to = c("F", "F", "N0", "N1", "G", "N0", "N2", "H", "N1", "N2"), class = "special"),
    data.frame(from = rep(c("N1", "N2"), each = k), to = rep(U, 2), class = "block"),
    data.frame(from = rep(W, 2), to = rep(c("N1", "N2"), each = k), class = "block"),
    data.frame(from = "P1", to = "W1", class = "zigzag"),
    data.frame(from = U, to = W, class = "zigzag"),
    if (k >= 2) data.frame(from = paste0("U", 1:(k - 1)), to = paste0("W", 2:k), class = "zigzag") else NULL,
    data.frame(from = paste0("U", k), to = "H", class = "zigzag"))
}

# Section classes: path = zigzag arcs (including the two end arcs); hub = every arc between a hub
# and a vertex of the path; defect = the defect 4-cycle (drawn red even where it meets a hub);
# other = the rest.
sectionClasses = function(arcs, hubs, pathVertices) {
  cl = ifelse(arcs$class %in% c("zigzag", "terminal"), "path",
       ifelse(arcs$class == "defect", "defect",
       ifelse((arcs$from %in% hubs & arcs$to %in% pathVertices) |
              (arcs$to %in% hubs & arcs$from %in% pathVertices), "hub", "other")))
  arcs$class = cl
  arcs
}
col4 = c(path = "forestgreen", hub = "gray55", defect = "red", other = "black")

mkLabels = function(vn) parse(text = ifelse(grepl("[0-9]$", vn),
                              paste0(substr(vn, 1, 1), "[", substr(vn, 2, 3), "]"),
                              paste0("italic(", vn, ")")))

# Smallest distance, in plot units (igraph rescales the layout to [-1, 1]), between a vertex centre
# and an arc not incident to it.  A vertex of size 22 has radius 0.11 in these units, so an arc
# closer than that is drawn through the vertex.
vertexRadius = 22 / 200
clearance = function(g, lay) {
  L = norm_coords(lay); E = as_edgelist(g, names = FALSE); best = Inf
  for (e in seq_len(nrow(E))) {
    a = L[E[e, 1], ]; d = L[E[e, 2], ] - a
    for (v in setdiff(seq_len(nrow(L)), E[e, ])) {
      t = max(0, min(1, sum((L[v, ] - a) * d) / sum(d * d)))
      best = min(best, sqrt(sum((L[v, ] - a - t * d)^2)))
    }
  }
  best
}

plotSection = function(arcs, n, fname, seed, nPath, nHub) {
  g = graph_from_data_frame(arcs[, c("from", "to")], directed = TRUE)
  stopifnot(ecount(g) == 3 * n - 4, vcount(g) == n,
            all(degree(g, mode = "in") == degree(g, mode = "out")),
            sum(arcs$class == "path") == nPath, sum(arcs$class == "defect") == 4,
            sum(arcs$class == "hub") == nHub)
  set.seed(seed)
  lay = layout_with_kk(g, coords = matrix(runif(2 * vcount(g)), ncol = 2))
  cl = clearance(g, lay)
  if (cl <= vertexRadius)
    stop(sprintf("%s: an arc passes through a vertex (clearance %.3f <= radius %.3f)", fname, cl, vertexRadius))
  pdf(fname, width = 6.5, height = 6.5)
  par(mar = c(1.6, 0.5, 0.5, 0.5), xpd = NA)
  plot(g, layout = lay, vertex.color = "orange", vertex.label = mkLabels(V(g)$name),
       vertex.label.color = "navy", vertex.label.cex = 1.05, vertex.size = 22,
       edge.color = col4[arcs$class], edge.width = ifelse(arcs$class == "defect", 3.5, 1.4),
       edge.arrow.size = 0.5, edge.curved = 0.08)
  legend("bottomleft", legend = c("zigzag path", "at a hub", "defect 4-cycle", "other"),
         col = col4[c("path", "hub", "defect", "other")], lwd = 3, cex = 0.85, bty = "n")
  dev.off()
  cat(fname, "written\n")
}

k = 2  # G_10: path T0 U1 W1 U2 W2 T3, hubs T1 T2
aG = sectionClasses(familyG(k), c("T1", "T2"), c("T0", "T3", paste0("U", 1:k), paste0("W", 1:k)))
plotSection(aG, 10, "ObstacleG10.pdf", 43, 2 * k + 1, 4 * k + 4)
k = 1  # H_11: path P1 W1 U1 H, hubs N1 N2; the hub arc N1 -> P1 is on the defect 4-cycle
aH = sectionClasses(familyH(k), c("N1", "N2"), c("P1", "H", paste0("U", 1:k), paste0("W", 1:k)))
plotSection(aH, 11, "ObstacleH11.pdf", 134, 2 * k + 1, 4 * k + 4 - 1)
