# Figures fig:g8-h9 and fig:family of paper 1: the obstacles G_8, H_9 (Section sec:threshold3) and
# G_10, H_11 (Section sec:family), drawn alike so that the family resemblance shows. All four
# panels share one skeleton: the four core vertices (T_i or N_i) and P_1, P_2 have the same
# coordinates in every panel, so the defect 4-cycle is drawn identically; the zigzag path runs
# down the right-hand side (G_n, from T_0 to T_3) or from P_1 round the right to H (H_n). The
# positions of F, G, H and of the bend were chosen by a search maximising the clearance below. Arcs are coloured
# by the classes of Section sec:family: the zigzag path, the arcs at the two hubs, the defect
# 4-cycle and the other arcs. Writes into the directory it is run from. The arc counts, the
# Eulerian property, the class sizes, and that no arc passes through a vertex other than its
# ends, are checked before plotting.
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
familyH = function(k) {  # H_n, n = 9 + 2k
  U = if (k >= 1) paste0("U", 1:k) else character(0); W = if (k >= 1) paste0("W", 1:k) else character(0)
  rbind(
    data.frame(from = c("N0", "N0", "N1", "N1", "N2"), to = c("N2", "N3", "N2", "N3", "N3"), class = "core"),
    data.frame(from = c("N2", "N2", "P2"), to = c("P1", "P2", "G"), class = "port"),
    data.frame(from = c("N0", "P2", "N1", "P1"), to = c("P2", "N1", "P1", "N0"), class = "defect"),
    data.frame(from = c("N2", "N3", "F", "F", "N3", "G", "G", "N3", "H", "H"),
               to = c("F", "F", "N0", "N1", "G", "N0", "N2", "H", "N1", "N2"), class = "special"),
    if (k >= 1) data.frame(from = rep(c("N1", "N2"), each = k), to = rep(U, 2), class = "block") else NULL,
    if (k >= 1) data.frame(from = rep(W, 2), to = rep(c("N1", "N2"), each = k), class = "block") else NULL,
    if (k >= 1) data.frame(from = "P1", to = "W1", class = "zigzag") else NULL,
    if (k >= 1) data.frame(from = U, to = W, class = "zigzag") else NULL,
    if (k >= 2) data.frame(from = paste0("U", 1:(k - 1)), to = paste0("W", 2:k), class = "zigzag") else NULL,
    data.frame(from = if (k >= 1) paste0("U", k) else "P1", to = "H", class = "zigzag"))
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


# Shared skeleton. The cores are not isomorphic, so the roles c1..c4 only fix positions: c1, c2
# are the defect 4-cycle's core vertices, c3 and c4 the rest of the core.
roles = list(G = c(T1 = "c1", T2 = "c2", T0 = "c3", T3 = "c4"),
             H = c(N0 = "c1", N1 = "c2", N2 = "c3", N3 = "c4"))
skeleton = rbind(c1 = c(-1.25, 0), c2 = c(1.25, 0), P2 = c(0, 0.85), P1 = c(0, -0.85),
                 c3 = c(-0.55, 2.0), c4 = c(0.55, -2.0))
famCoords = function(fam, k) {
  M = skeleton; inv = setNames(names(roles[[fam]]), roles[[fam]])
  rownames(M) = ifelse(rownames(M) %in% names(inv), inv[rownames(M)], rownames(M))
  if (fam == "H") M = rbind(M, F = c(-0.5, -1.75), G = c(2.75, 1.25), H = c(3.0, 2.25))
  if (k == 0) return(M)
  # the 2k path vertices in path order, alternating sides so the zigzag shows
  pv = as.vector(rbind(paste0(if (fam == "G") "U" else "W", 1:k), paste0(if (fam == "G") "W" else "U", 1:k)))
  side = ifelse(seq_along(pv) %% 2 == 1, 1, -1)
  P = if (fam == "G") {
    cbind(2.35 - 0.2 * side, if (k == 1) c(1.15, -1.15) else seq(1.6, -1.6, length.out = 2 * k))
  } else {
    # along the quadratic Bezier curve from P1 to H with control point bend, strictly inside it
    t = seq(0, 1, length.out = 2 * k + 2)[2:(2 * k + 1)]; bend = c(2.25, 2.75)
    xy = outer((1 - t)^2, M["P1", ]) + outer(2 * t * (1 - t), bend) + outer(t^2, M["H", ])
    cbind(xy[, 1], xy[, 2] + 0.2 * side)
  }
  rownames(P) = pv
  rbind(M, P)
}
# one normalisation for every panel, so the skeleton sits at the same place on each page
allPts = rbind(famCoords("G", 2), famCoords("H", 1))
centre = (apply(allPts, 2, max) + apply(allPts, 2, min)) / 2
halfWidth = 1.08 * max(abs(sweep(allPts, 2, centre)))

vertexSize = 18
vertexRadius = vertexSize / 200          # in the [-1, 1] plot units used with rescale = FALSE
clearance = function(g, L) {
  E = as_edgelist(g, names = FALSE); best = Inf
  for (e in seq_len(nrow(E))) {
    a = L[E[e, 1], ]; d = L[E[e, 2], ] - a
    for (v in setdiff(seq_len(nrow(L)), E[e, ])) {
      t = max(0, min(1, sum((L[v, ] - a) * d) / sum(d * d)))
      best = min(best, sqrt(sum((L[v, ] - a - t * d)^2)))
    }
  }
  best
}

plotMember = function(fam, k, fname) {
  n = if (fam == "G") 6 + 2 * k else 9 + 2 * k
  arcs = if (fam == "G") familyG(k) else familyH(k)
  idx = seq_len(k)
  if (fam == "G") {
    hubs = c("T1", "T2"); pathV = c("T0", "T3", paste0("U", idx), paste0("W", idx))
  } else {
    hubs = c("N1", "N2"); pathV = c("P1", "H", paste0("U", idx), paste0("W", idx))
  }
  a = sectionClasses(arcs, hubs, pathV)
  g = graph_from_data_frame(a[, c("from", "to")], directed = TRUE)
  # H_n: the hub arc N1 -> P1 lies on the defect 4-cycle and is drawn with it
  nHub = 4 * k + 4 - (fam == "H")
  stopifnot(ecount(g) == 3 * n - 4, vcount(g) == n,
            all(degree(g, mode = "in") == degree(g, mode = "out")),
            sum(a$class == "path") == 2 * k + 1, sum(a$class == "defect") == 4,
            sum(a$class == "hub") == nHub)
  L = sweep(famCoords(fam, k)[V(g)$name, ], 2, centre) / halfWidth
  cl = clearance(g, L)
  if (cl <= vertexRadius)
    stop(sprintf("%s: an arc passes through a vertex (clearance %.3f <= radius %.3f)", fname, cl, vertexRadius))
  pdf(fname, width = 6.5, height = 6.5)
  par(mar = c(2.2, 0.5, 0.5, 0.5), xpd = NA)
  plot(g, layout = L, rescale = FALSE, xlim = c(-1, 1), ylim = c(-1, 1), asp = 1,
       vertex.color = "orange", vertex.label = mkLabels(V(g)$name), vertex.label.color = "navy",
       vertex.label.cex = 1.05, vertex.size = vertexSize, edge.color = col4[a$class],
       edge.width = ifelse(a$class == "defect", 3.5, 1.4), edge.arrow.size = 0.5, edge.curved = 0.08)
  legend(x = 0, y = -1.06, xjust = 0.5, yjust = 1, horiz = TRUE,
         legend = c("zigzag path", "at a hub", "defect 4-cycle", "other"),
         col = col4[c("path", "hub", "defect", "other")], lwd = 3, cex = 0.85, bty = "n")
  dev.off()
  cat(sprintf("%s written (clearance %.3f > vertex radius %.3f)\n", fname, cl, vertexRadius))
}

plotMember("G", 1, "ObstacleG8.pdf")
plotMember("H", 0, "ObstacleH9.pdf")
plotMember("G", 2, "ObstacleG10.pdf")
plotMember("H", 1, "ObstacleH11.pdf")
