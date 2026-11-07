# Draws the obstacle classes of the two minimum containment covers in covers.tsv:
#   A' -- the 26 classes covering the 17,674 non-3-inducible 9-tournaments (G8 and 25 others);
#   B' -- the 25 signed classes covering the 254 tournaments that are 3-inducible but not with unit margin.
# A class covers a tournament under containment when the tournament contains the class's arcs.
#
# Each class is drawn as its multidigraph: an arc's label is its multiplicity when that is not 1
# (dual weight = multiplicity / sum of multiplicities), and a red dashed arc has negative weight.
# Vertices keep the numbering of the arclist column of the catalogue file.
#
# Inputs (this folder): covers.tsv (covers.py), n9_minimal_obstacles.tsv and n9_signed_obstacles_254.tsv
# (build_catalogue.py).
# Output: figures/A_prime.pdf and figures/B_prime.pdf (one panel per class), and
# figures/A_prime/<id>.pdf, figures/B_prime/<id>.pdf (one page per class).
# Run from this folder:  Rscript draw_covers.R
library(igraph)

readClasses = function(path) {
  d = read.delim(path, colClasses = "character")
  stopifnot(!anyDuplicated(d$id))
  split(d, d$id)
}

classGraph = function(row) {
  parts = strsplit(strsplit(row$arclist, ";", fixed = TRUE)[[1]], "[>:]")
  arcs = t(sapply(parts, function(p) as.integer(p)))
  m = arcs[, 3]
  stopifnot(sum(abs(m)) == as.integer(row$total_mult), nrow(arcs) == as.integer(row$arcs))
  verts = sort(unique(c(arcs[, 1], arcs[, 2])))
  stopifnot(length(verts) == as.integer(row$verts))
  g = graph_from_data_frame(data.frame(from = as.character(arcs[, 1]), to = as.character(arcs[, 2]), m = m),
                            vertices = data.frame(name = as.character(verts)))
  g
}

drawClass = function(g, title) {
  set.seed(1)                                   # layout_with_kk starts from a random layout
  lay = layout_with_kk(g)
  m = E(g)$m
  plot(g, layout = lay, vertex.color = "orange", vertex.label.color = "navy", vertex.size = 20,
       vertex.label.cex = 0.9, edge.color = ifelse(m < 0, "red3", "grey30"), edge.lty = ifelse(m < 0, 2, 1),
       edge.width = 1.2, edge.arrow.size = 0.4, edge.label = ifelse(abs(m) == 1, NA, abs(m)),
       edge.label.color = "black", edge.label.cex = 0.85, main = title, cex.main = 1)
}

drawCover = function(ids, classes, valueName, stem) {
  missing = setdiff(ids, names(classes))
  if (length(missing)) stop(sprintf("%s: classes not in the catalogue: %s", stem, paste(missing, collapse = " ")))
  titles = lapply(ids, function(i) bquote(.(i) ~~~ alpha^.(valueName) == .(classes[[i]]$alpha)))
  graphs = lapply(ids, function(i) classGraph(classes[[i]]))
  ncol = 5; nrow = ceiling(length(ids) / ncol)
  pdf(file.path("figures", paste0(stem, ".pdf")), width = 3 * ncol, height = 3.2 * nrow)
  par(mfrow = c(nrow, ncol), mar = c(0.3, 0.3, 1.6, 0.3))
  for (k in seq_along(ids)) drawClass(graphs[[k]], titles[[k]])
  dev.off()
  dir.create(file.path("figures", stem), showWarnings = FALSE)
  for (k in seq_along(ids)) {
    pdf(file.path("figures", stem, paste0(ids[k], ".pdf")), width = 5, height = 5.3)
    par(mar = c(0.3, 0.3, 1.6, 0.3))
    drawClass(graphs[[k]], titles[[k]])
    dev.off()
  }
  cat(sprintf("figures/%s.pdf and figures/%s/: %d classes\n", stem, stem, length(ids)))
}

covers = read.delim("covers.tsv", colClasses = "character")
coverIds = function(coll) {
  r = covers[covers$collection == coll & covers$reading == "M", ]
  stopifnot(nrow(r) == 1)
  ids = strsplit(r$ids, " ", fixed = TRUE)[[1]]
  stopifnot(length(ids) == as.integer(r$n_classes))
  ids
}

dir.create("figures", showWarnings = FALSE)
drawCover(coverIds("17674"), readClasses("n9_minimal_obstacles.tsv"), "*", "A_prime")
drawCover(coverIds("254"), readClasses("n9_signed_obstacles_254.tsv"), "=", "B_prime")
