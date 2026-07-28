# cA3.pdf (manuscript Figure 5, Counterexample 5.2): the unique regular
# counterexample to A(3) at n = 11 -- the circulant tournament on Z_11 with
# connection set S = {1,2,3,4,6} (arc u -> v iff (v-u) mod 11 in S).
# The drawing places the residues 0..10 on a circle (0 at top, clockwise) and
# colours each arc by its step (v-u) mod 11, so the five translation-classes of
# arcs -- the connection set that defines the tournament -- are visible, and the
# C_11 rotational symmetry (Aut(cA3) = C_11) is manifest.
#
# Self-verification before plotting: (a) exactly one arc per pair (tournament);
# (b) regular, every out-degree 5; (c) the six-order 2/3-certificate of
# Appendix D makes every one of the 55 arcs forward in exactly 4 of the 6 orders
# (all arcs tight at 4/6 = 2/3), so alpha* = 2/3. The script stops on any mismatch.
library(igraph)
# outputs are written to the working directory -- run this script from its own folder

n = 11
S = c(1, 2, 3, 4, 6)

# build the circulant (residues 0..10 <-> internal vertices 1..11)
adj = matrix(FALSE, n, n)
for (u in 0:10) for (s in S) {
  v = (u + s) %% 11
  adj[u + 1, v + 1] = TRUE
}
for (i in 1:(n - 1)) for (j in (i + 1):n) stopifnot(adj[i, j] + adj[j, i] == 1)  # tournament
stopifnot(all(rowSums(adj) == 5))                                                # regular

# the six-order 2/3-certificate (Appendix D; residue labels, earliest first)
orders = list(
  c(10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9),
  c( 4, 5, 6, 7, 8, 9,10, 0, 1, 2, 3),
  c( 7, 9, 0, 2, 4, 6, 8,10, 1, 3, 5),
  c( 8,10, 1, 3, 5, 7, 9, 0, 2, 4, 6),
  c( 2, 5, 8, 0, 3, 6, 9, 1, 4, 7,10),
  c( 3, 6, 9, 1, 4, 7,10, 2, 5, 8, 0))
fwd = matrix(0L, n, n)
for (O in orders) {
  pos = integer(n); pos[O + 1] = 1:n
  for (u in 0:10) for (v in 0:10) if (adj[u + 1, v + 1] && pos[u + 1] < pos[v + 1])
    fwd[u + 1, v + 1] = fwd[u + 1, v + 1] + 1L
}
stopifnot(all(fwd[adj] == 4))    # every arc forward in exactly 4/6 orders => alpha* = 2/3
cat("cA3 checks passed: tournament, regular (out-deg 5), all 55 arcs tight at 4/6 = 2/3\n")

# edge list, coloured by step class
pal = c("1" = "#000000", "2" = "#0072B2", "3" = "#009E73",
        "4" = "#CC79A7", "6" = "#D55E00")
edges = NULL; ecol = NULL
for (u in 0:10) for (s in S) {
  v = (u + s) %% 11
  edges = rbind(edges, c(u + 1, v + 1))
  ecol = c(ecol, pal[as.character(s)])
}
g = graph_from_edgelist(edges, directed = TRUE)

# circle layout: residue r at angle pi/2 - 2*pi*r/11 (residue 0 at top, clockwise)
lay = matrix(0, n, 2)
for (i in 1:n) {
  ang = pi / 2 - 2 * pi * (i - 1) / n
  lay[i, ] = c(cos(ang), sin(ang))
}

pdf("cA3.pdf", width = 6.5, height = 7.3)
par(mar = c(0.5, 0.4, 0.4, 0.4), xpd = NA)
# widen the y-window below the unit circle so the legend sits in clear space,
# well below vertices 5 and 6 (which lie at the bottom of the circle)
plot(g, layout = lay, ylim = c(-1.72, 1.03),
     vertex.color = "orange", vertex.label = 0:10,
     vertex.label.color = "navy", vertex.label.cex = 1.5, vertex.size = 20,
     edge.color = ecol, edge.width = 1.7, edge.arrow.size = 0.5, edge.curved = 0)
legend(x = 0, y = -1.30, xjust = 0.5, yjust = 1, horiz = TRUE,
       legend = paste0("s = ", names(pal)), col = pal, lwd = 2.6,
       bty = "n", cex = 1.05, seg.len = 1.4,
       title = expression("arc class:  (v - u) mod 11 = s"))
dev.off()
cat("cA3.pdf written\n")
