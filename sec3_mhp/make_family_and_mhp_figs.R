# Figure fig:mhp of paper 1 (the obstacles G_8, H_9, G_10, H_11 are drawn by
# make_family_section_figs.R):
#   MHP_Fig1 -- weighted majority tournament of Counterexample cex:weak-strong for both
#     m = 7 and m = 9 (they differ only in the margin of 3 > 4, labelled "3 (5)"),
#     minimum-weight FASs highlighted (Figure fig:mhp, panel a).
#   MHP_Fig2 -- weighted majority tournament of Counterexample cex:strong-m5 (m = 5,
#     n = 6), unique minimum-weight FAS highlighted, e = (4,2) thick red.
# Every FAS/margin claim drawn here is re-verified by brute force before
# plotting; the script stops on any mismatch.
library(igraph)
# outputs are written to the working directory -- run this script from its own folder

## ---------- shared helpers ----------

plotStyled = function(g, layout, labels, ecol, ewid, elty, fname, elabels = NULL,
                      legendItems = NULL, legendCols = NULL, vsize = 22,
                      arrowSize = 0.5, curved = 0.08, labelPos = NULL,
                      omitLabel = NULL) {
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
    # arcs whose label equals omitLabel (the margin-1 arcs) are left unlabelled
    keep = !(as.character(elabels) %in% omitLabel)
    elabels = elabels[keep]; labelPos = labelPos[keep, , drop = FALSE]
    # weight labels off the arcs, on white discs so they never blend into a line
    long = nchar(as.character(elabels)) > 1
    points(labelPos[!long, 1], labelPos[!long, 2], pch = 21, col = NA, bg = "white", cex = 2.9)
    if (any(long)) {
      w = strwidth(elabels[long], cex = 1.1) / 2 + 0.03
      h = strheight("0", cex = 1.1) / 2 + 0.04
      rect(labelPos[long, 1] - w, labelPos[long, 2] - h, labelPos[long, 1] + w,
           labelPos[long, 2] + h, col = "white", border = NA)
    }
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

## ---------- Counterexample cex:weak-strong (Figure fig:mhp, panel a) ----------

# Seven voters (3, 2, 2) and nine voters (4, 3, 2) give the same tournament T_1 with the same
# margins except on 3 > 4 (3 and 5); one drawing shows both, the nine-voter margin in parentheses.
voters = list(c(2, 3, 4, 1), c(1, 3, 4, 2), c(4, 1, 2, 3))
T1 = arcKey(rbind(c(1,2), c(2,3), c(3,4), c(4,1), c(1,3), c(4,2)))
target = arcKey(rbind(c(1,2), c(1,3), c(4,2)))
wm7 = weightedMajority(voters, c(3, 2, 2), 4)
wm9 = weightedMajority(voters, c(4, 3, 2), 4)
stopifnot(arcKey(wm7$edges) == T1, arcKey(wm9$edges) == T1)
key7 = paste(wm7$edges[, 1], wm7$edges[, 2], sep = ">")
key9 = paste(wm9$edges[, 1], wm9$edges[, 2], sep = ">")
w9 = wm9$weights[match(key7, key9)]
stopifnot(identical(which(wm7$weights != w9), which(key7 == "3>4")))   # the only margin that differs
res7 = bruteMinFAS(wm7$edges, wm7$weights, 4)
res9 = bruteMinFAS(wm9$edges, wm9$weights, 4)
stopifnot(length(res7$sets) == 2, target %in% res7$sets, "3>4" %in% res7$sets,
          length(res9$sets) == 1, res9$sets == target)
cat("MHP_Fig1: seven voters, min-weight FAS value", res7$value, "| optimal sets:", length(res7$sets),
    "; nine voters, value", res9$value, "| optimal sets:", length(res9$sets), "\n")
g = graph_from_edgelist(wm7$edges, directed = TRUE)
ecol = rep("gray55", ecount(g)); ewid = rep(1.6, ecount(g)); elty = rep(1, ecount(g))
ecol[key7 %in% c("1>2", "1>3", "4>2")] = "black"
ewid[key7 %in% c("1>2", "1>3", "4>2")] = 3.5
elty[key7 == "3>4"] = 2   # the alternative minimum-weight FAS of the seven-voter profile, dashed
labs = ifelse(wm7$weights == w9, as.character(wm7$weights), paste0(wm7$weights, " (", w9, ")"))
lay = layout_in_circle(g)
plotStyled(g, lay, 1:4, ecol, ewid, elty, "MHP_Fig1.pdf",
           elabels = labs, vsize = 20, arrowSize = 0.85, curved = 0,
           labelPos = edgeLabelPos(lay, wm7$edges), omitLabel = "1")

## ---------- Counterexample cex:strong-m5 (Figure fig:mhp, panel b) ----------

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
           arrowSize = 0.8, curved = 0, labelPos = edgeLabelPos(lay6, wm6$edges), omitLabel = "1")
