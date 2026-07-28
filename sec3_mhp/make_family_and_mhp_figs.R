# Figures for the v3.0 manuscript:
#   ObstacleG8 / ObstacleG10 / ObstacleH9 / ObstacleH11 -- the Section 9 family
#     members, drawn in the style of the original ObstructionC8.pdf (organic
#     layout, orange vertices, navy labels) but with role-labelled vertices and
#     arcs coloured by class; the defect 4-cycle is thick red.
#   MHP_Fig1a / MHP_Fig1b -- weighted majority tournament of Counterexample 3.1
#     (m = 7 and m = 9), weights on arcs, minimum-weight FASs highlighted.
#   MHP_Fig2 -- weighted majority tournament of Counterexample 3.2 (m = 5,
#     n = 6), unique minimum-weight FAS highlighted, e = (4,2) thick red.
# Every FAS/margin claim drawn here is re-verified by brute force before
# plotting; the script stops on any mismatch.
library(igraph)
# outputs are written to the working directory -- run this script from its own folder

## ---------- shared helpers ----------

plotStyled = function(g, layout, labels, ecol, ewid, elty, fname, elabels = NULL,
                      legendItems = NULL, legendCols = NULL, vsize = 22,
                      arrowSize = 0.5, curved = 0.08, labelPos = NULL) {
  pdf(fname, width = 6.5, height = 6.5)
  par(mar = c(1.6, 0.5, 0.5, 0.5), xpd = NA)
  plot(g, layout = layout,
       vertex.color = "orange", vertex.label = labels,
       vertex.label.color = "navy", vertex.label.cex = 1.05,
       vertex.size = vsize,
       edge.color = ecol, edge.width = ewid, edge.lty = elty,
       edge.label = if (is.null(labelPos)) elabels else NA,
       edge.label.color = "black", edge.label.cex = 1.05,
       edge.arrow.size = arrowSize, edge.curved = curved)
  if (!is.null(labelPos)) {
    # weight labels off the arcs, on white discs so they never blend into a line
    points(labelPos[, 1], labelPos[, 2], pch = 21, col = NA, bg = "white", cex = 2.9)
    text(labelPos[, 1], labelPos[, 2], elabels, cex = 1.1)
  }
  if (!is.null(legendItems)) {
    legend("bottomleft", legend = legendItems, col = legendCols, lwd = 3,
           cex = 0.85, bty = "n", horiz = FALSE)
  }
  dev.off()
  cat(fname, "written\n")
}

# label anchor for each (straight) arc: 35% of the way from tail to head, pushed
# off the line on the side pointing away from the layout's centre; keeps the two
# crossing-diagonal labels of a circle layout apart and off the thick arcs
edgeLabelPos = function(layout, edges, tfrac = 0.35, off = 0.10) {
  out = matrix(0, nrow(edges), 2)
  for (r in 1:nrow(edges)) {
    p1 = layout[edges[r, 1], ]; p2 = layout[edges[r, 2], ]
    base = p1 + tfrac * (p2 - p1)
    d = (p2 - p1) / sqrt(sum((p2 - p1)^2))
    perp = c(-d[2], d[1])
    if (sum(perp * base) < 0) perp = -perp
    out[r, ] = base + off * perp
  }
  out
}

allPerms = function(n) {
  if (n == 1) return(list(1L))
  smaller = allPerms(n - 1)
  out = list()
  for (p in smaller) for (pos in 0:(n - 1)) {
    out[[length(out) + 1]] = append(p, n, after = pos)
  }
  out
}

# minimum-weight FAS of a weighted tournament by brute force over all orders;
# returns the optimal backward-arc sets (as sorted "u>v" strings)
bruteMinFAS = function(edges, weights, n) {
  perms = allPerms(n)
  best = Inf
  optSets = list()
  for (p in perms) {
    pos = order(p)  # pos[v] = position of v in the order p... careful below
    pos = match(1:n, p)
    backIdx = which(pos[edges[, 1]] > pos[edges[, 2]])
    w = sum(weights[backIdx])
    key = paste(sort(paste(edges[backIdx, 1], edges[backIdx, 2], sep = ">")),
                collapse = ",")
    if (w < best - 1e-9) { best = w; optSets = list(key) }
    else if (abs(w - best) < 1e-9 && !(key %in% optSets)) {
      optSets = c(optSets, key)
    }
  }
  list(value = best, sets = unlist(optSets))
}

arcKey = function(arcs) paste(sort(paste(arcs[, 1], arcs[, 2], sep = ">")),
                              collapse = ",")

# weighted majority tournament from voters (list of orders) and multiplicities
weightedMajority = function(voters, mult, n) {
  L = matrix(0, n, n)
  for (r in seq_along(voters)) {
    v = voters[[r]]
    for (a in 1:(n - 1)) for (b in (a + 1):n) {
      L[v[a], v[b]] = L[v[a], v[b]] + mult[r]
    }
  }
  edges = NULL; weights = NULL
  for (i in 1:(n - 1)) for (j in (i + 1):n) {
    stopifnot(L[i, j] != L[j, i])
    if (L[i, j] > L[j, i]) { edges = rbind(edges, c(i, j)) }
    else { edges = rbind(edges, c(j, i)) }
    weights = c(weights, abs(L[i, j] - L[j, i]))
  }
  list(edges = edges, weights = weights)
}

## ---------- Section 9 family members ----------

familyG = function(k) {  # G_n, n = 6 + 2k
  U = paste0("U", 1:k); W = paste0("W", 1:k)
  arcs = rbind(
    data.frame(from = "T0", to = c("T1", "T2", "T3"), class = "core"),
    data.frame(from = c("T1", "T2"), to = "T3", class = "core"),
    data.frame(from = c("T3", "P1", "T3", "P2"),
               to = c("P1", "T0", "P2", "T0"), class = "port"),
    data.frame(from = c("T1", "P2", "T2", "P1"),
               to = c("P2", "T2", "P1", "T1"), class = "defect"),
    data.frame(from = rep(c("T1", "T2"), each = k), to = rep(U, 2), class = "block"),
    data.frame(from = rep(W, 2), to = rep(c("T1", "T2"), each = k), class = "block"),
    data.frame(from = "U1", to = "W1", class = "zigzag"),
    if (k >= 2) data.frame(from = rep(paste0("U", 2:k), 2),
                           to = c(paste0("W", 1:(k - 1)), paste0("W", 2:k)),
                           class = "zigzag") else NULL,
    data.frame(from = c("U1", "T3"), to = c("T0", W[k]), class = "terminal"))
  arcs
}

familyH = function(k) {  # H_n, n = 9 + 2k
  arcs = rbind(
    data.frame(from = c("N0", "N0", "N1", "N1", "N2"),
               to = c("N2", "N3", "N2", "N3", "N3"), class = "core"),
    data.frame(from = c("N2", "N2", "P2"),
               to = c("P1", "P2", "G"), class = "port"),
    data.frame(from = c("N0", "P2", "N1", "P1"),
               to = c("P2", "N1", "P1", "N0"), class = "defect"),
    data.frame(from = c("N2", "N3", "F", "F", "N3", "G", "G", "N3", "H", "H"),
               to = c("F", "F", "N0", "N1", "G", "N0", "N2", "H", "N1", "N2"),
               class = "special"))
  if (k >= 1) {
    U = paste0("U", 1:k); W = paste0("W", 1:k)
    arcs = rbind(arcs,
      data.frame(from = rep(c("N1", "N2"), each = k), to = rep(U, 2), class = "block"),
      data.frame(from = rep(W, 2), to = rep(c("N1", "N2"), each = k), class = "block"),
      data.frame(from = "P1", to = "W1", class = "zigzag"),
      data.frame(from = U, to = W, class = "zigzag"),
      if (k >= 2) data.frame(from = paste0("U", 1:(k - 1)),
                             to = paste0("W", 2:k), class = "zigzag") else NULL,
      data.frame(from = paste0("U", k), to = "H", class = "zigzag"))
  } else {
    arcs = rbind(arcs, data.frame(from = "P1", to = "H", class = "zigzag"))
  }
  arcs
}

classColor = c(core = "black", port = "dodgerblue3", defect = "red",
               block = "gray55", zigzag = "forestgreen",
               terminal = "purple3", special = "purple3")

mkLabels = function(vn) parse(text = ifelse(grepl("[0-9]$", vn),
                              paste0(substr(vn, 1, 1), "[", substr(vn, 2, 3), "]"),
                              paste0("italic(", vn, ")")))

# kk layout -- used for the family members shown only in the companion paper
# (ObstacleG10, ObstacleH11), which keep their canonical T-/N- vertex names.
plotFamily = function(arcs, n, fname, seed, legendItems, legendCols) {
  g = graph_from_data_frame(arcs[, c("from", "to")], directed = TRUE)
  stopifnot(ecount(g) == 3 * n - 4, vcount(g) == n)
  stopifnot(all(degree(g, mode = "in") == degree(g, mode = "out")))  # Eulerian
  ecol = classColor[arcs$class]
  ewid = ifelse(arcs$class == "defect", 3.5, 1.4)
  set.seed(seed)
  plotStyled(g, layout_with_kk(g), mkLabels(V(g)$name), ecol, ewid,
             rep(1, ecount(g)), fname, legendItems = legendItems,
             legendCols = legendCols)
}

# Aligned, core-relabelled layout for the two Figure-6 panels (G8 and H9 = "G9").
# The four core vertices are relabelled c1..c4 (c1,c2 the two on the defect
# 4-cycle), and the shared skeleton {c1,c2,c3,c4,P1,P2} is given IDENTICAL
# coordinates in both panels, so the thick-red defect 4-cycle
# c1 -> P2 -> c2 -> P1 -> c1 is drawn identically and the panels are exactly
# aligned on their common part. Family-specific vertices (G8: coset U1,W1;
# H9: special F,G,H) sit to the right. Cores are non-isomorphic, so c1..c4 is a
# role labelling, not a vertex isomorphism.
mapG = c(T1 = "c1", T2 = "c2", T0 = "c3", T3 = "c4")
mapH = c(N0 = "c1", N1 = "c2", N2 = "c3", N3 = "c4")
relabelArcs = function(arcs, map) {
  ren = function(x) ifelse(x %in% names(map), map[x], x)
  arcs$from = ren(arcs$from); arcs$to = ren(arcs$to); arcs
}
coreShared = matrix(c(
  -1.25,  0.00,    # c1  (defect, left)
   1.25,  0.00,    # c2  (defect, right)
   0.00,  0.85,    # P2  (defect/port, top)
   0.00, -0.85,    # P1  (defect/port, bottom)
  -0.55,  2.00,    # c3  (rest of core, top)
   0.55, -2.00),   # c4  (rest of core, bottom)
  ncol = 2, byrow = TRUE, dimnames = list(c("c1","c2","P2","P1","c3","c4"), NULL))
coordsG8 = rbind(coreShared, matrix(c(2.35, 1.15,  2.35, -1.15),
  ncol = 2, byrow = TRUE, dimnames = list(c("U1","W1"), NULL)))
coordsH9 = rbind(coreShared, matrix(c(2.05, 0.00,  2.45, 1.25,  2.45, -1.25),
  ncol = 2, byrow = TRUE, dimnames = list(c("F","G","H"), NULL)))
# one common normalization to [-1,1] (same transform for both => exact alignment)
allpts = rbind(coordsG8, coordsH9)
ctr = c((max(allpts[,1]) + min(allpts[,1]))/2, (max(allpts[,2]) + min(allpts[,2]))/2)
half = 1.12 * max(abs(allpts[,1] - ctr[1]), abs(allpts[,2] - ctr[2]))
normc = function(M) cbind((M[,1] - ctr[1]) / half, (M[,2] - ctr[2]) / half)

plotAligned = function(arcs, n, fname, map, coords, legendItems, legendCols) {
  arcs = relabelArcs(arcs, map)
  g = graph_from_data_frame(arcs[, c("from", "to")], directed = TRUE)
  stopifnot(ecount(g) == 3 * n - 4, vcount(g) == n,
            setequal(V(g)$name, rownames(coords)),
            all(degree(g, mode = "in") == degree(g, mode = "out")))  # Eulerian
  ecol = classColor[arcs$class]
  ewid = ifelse(arcs$class == "defect", 3.5, 1.4)
  pdf(fname, width = 6.5, height = 6.5)
  par(mar = c(1.6, 0.5, 0.5, 0.5), xpd = NA)
  plot(g, layout = normc(coords[V(g)$name, ]),
       rescale = FALSE, xlim = c(-1, 1), ylim = c(-1, 1), asp = 1,
       vertex.color = "orange", vertex.label = mkLabels(V(g)$name),
       vertex.label.color = "navy", vertex.label.cex = 1.05, vertex.size = 22,
       edge.color = ecol, edge.width = ewid, edge.arrow.size = 0.5, edge.curved = 0.08)
  legend("bottomleft", legend = legendItems, col = legendCols, lwd = 3,
         cex = 0.85, bty = "n", horiz = FALSE)
  dev.off()
  cat(fname, "written\n")
}

legG   = c("core", "port", "defect 4-cycle", "coset (block)", "zigzag", "terminal")
colG   = classColor[c("core", "port", "defect", "block", "zigzag", "terminal")]
legH9  = c("core", "port", "defect 4-cycle", "coset (special)", "zigzag")
colH9  = classColor[c("core", "port", "defect", "special", "zigzag")]
legH11 = c("core", "port", "defect 4-cycle", "block", "zigzag", "special")
colH11 = classColor[c("core", "port", "defect", "block", "zigzag", "special")]

plotAligned(familyG(1), 8, "ObstacleG8.pdf", mapG, coordsG8, legG, colG)
plotAligned(familyH(0), 9, "ObstacleH9.pdf", mapH, coordsH9, legH9, colH9)
plotFamily(familyG(2), 10, "ObstacleG10.pdf", 11, legG,   colG)
plotFamily(familyH(1), 11, "ObstacleH11.pdf", 3, legH11, colH11)

## ---------- Counterexample 3.1 (Figure 1a, 1b) ----------

voters = list(c(2, 3, 4, 1), c(1, 3, 4, 2), c(4, 1, 2, 3))
for (case in list(list(mult = c(3, 2, 2), fname = "MHP_Fig1a.pdf",
                       nsets = 2, unique = FALSE),
                  list(mult = c(4, 3, 2), fname = "MHP_Fig1b.pdf",
                       nsets = 1, unique = TRUE))) {
  wm = weightedMajority(voters, case$mult, 4)
  # the majority tournament must be T_1 regardless of multiplicities
  stopifnot(arcKey(wm$edges) ==
            arcKey(rbind(c(1,2), c(2,3), c(3,4), c(4,1), c(1,3), c(4,2))))
  res = bruteMinFAS(wm$edges, wm$weights, 4)
  target = arcKey(rbind(c(1,2), c(1,3), c(4,2)))
  stopifnot(length(res$sets) == case$nsets, target %in% res$sets)
  if (!case$unique) stopifnot("3>4" %in% res$sets)
  cat(case$fname, ": min-weight FAS value", res$value,
      "| optimal sets:", length(res$sets), "\n")
  g = graph_from_edgelist(wm$edges, directed = TRUE)
  key = paste(wm$edges[, 1], wm$edges[, 2], sep = ">")
  ecol = rep("gray55", ecount(g)); ewid = rep(1.6, ecount(g))
  elty = rep(1, ecount(g))
  ecol[key %in% c("1>2", "1>3", "4>2")] = "black"
  ewid[key %in% c("1>2", "1>3", "4>2")] = 3.5
  if (!case$unique) elty[key == "3>4"] = 2   # the tied alternative FAS, dashed
  lay = layout_in_circle(g)
  plotStyled(g, lay, 1:4, ecol, ewid, elty, case$fname,
             elabels = wm$weights, vsize = 20, arrowSize = 0.85, curved = 0,
             labelPos = edgeLabelPos(lay, wm$edges))
}

## ---------- Counterexample 3.2 (Figure 2) ----------

voters6 = list(c(2, 5, 3, 6, 1, 4), c(1, 4, 3, 6, 2, 5),
               c(4, 5, 3, 6, 1, 2), c(6, 1, 4, 2, 5, 3))
wm6 = weightedMajority(voters6, c(2, 1, 1, 1), 6)
res6 = bruteMinFAS(wm6$edges, wm6$weights, 6)
Fe = arcKey(rbind(c(1,2), c(4,2), c(4,3), c(4,5), c(6,2)))
stopifnot(length(res6$sets) == 1, res6$sets == Fe)
cat("MHP_Fig2: unique min-weight FAS confirmed, value", res6$value, "\n")
g6 = graph_from_edgelist(wm6$edges, directed = TRUE)
key6 = paste(wm6$edges[, 1], wm6$edges[, 2], sep = ">")
inFe = key6 %in% c("1>2", "4>2", "4>3", "4>5", "6>2")
ecol6 = rep("gray55", ecount(g6)); ecol6[inFe] = "black"
ecol6[key6 == "4>2"] = "red"
ewid6 = rep(1.4, ecount(g6)); ewid6[inFe] = 3.5
lay6 = layout_in_circle(g6)
plotStyled(g6, lay6, 1:6, ecol6, ewid6, rep(1, ecount(g6)),
           "MHP_Fig2.pdf", elabels = wm6$weights, vsize = 20,
           arrowSize = 0.8, curved = 0, labelPos = edgeLabelPos(lay6, wm6$edges))
