# Paley7.pdf (panel (b) of the cA3 figure, Section "threshold3"): Paley(7), the circulant
# tournament on Z_7 with connection set S = {1, 2, 4} (arc u -> v iff (v-u) mod 7 in S), drawn
# like cA3.pdf: residues on a circle (0 at top, clockwise), arcs coloured by step.
#
# Paley(7) is the n = 7 case of the circulant construction of Theorem thm:circulant-family
# (inverses e = (1, 2, 4) sum to 7), and the one case where three progressions, one of each
# step 1, 2, 4, induce it.  Self-verification before plotting: (a) tournament; (b) regular;
# (c) the three progressions P(0,1), P(4,2), P(5,4) have majority tournament Paley(7), and every
# arc is backward in exactly one of them.  The script stops on any mismatch.
library(igraph)
# writes Paley7.pdf into the current directory

n = 7
S = c(1, 2, 4)
adj = matrix(FALSE, n, n)
for (u in 0:(n - 1)) for (s in S) adj[u + 1, (u + s) %% n + 1] = TRUE
for (i in 1:(n - 1)) for (j in (i + 1):n) stopifnot(adj[i, j] + adj[j, i] == 1)   # tournament
stopifnot(all(rowSums(adj) == (n - 1) / 2))                                       # regular

prog = function(a, d) (a + (0:(n - 1)) * d) %% n
orders = list(prog(0, 1), prog(4, 2), prog(5, 4))
fwd = matrix(0L, n, n)
for (O in orders) {
  pos = integer(n); pos[O + 1] = 1:n
  for (u in 0:(n - 1)) for (v in 0:(n - 1)) if (adj[u + 1, v + 1] && pos[u + 1] < pos[v + 1])
    fwd[u + 1, v + 1] = fwd[u + 1, v + 1] + 1L
}
stopifnot(all(fwd[adj] == 2))    # every arc forward in exactly 2 of 3 voters: a unit-margin profile
cat("Paley(7) checks passed: tournament, regular, P(0,1), P(4,2), P(5,4) induce it with unit margin\n")

pal = c("1" = "#000000", "2" = "#0072B2", "4" = "#7B3294")
edges = NULL; ecol = NULL
for (u in 0:(n - 1)) for (s in S) {
  edges = rbind(edges, c(u + 1, (u + s) %% n + 1)); ecol = c(ecol, pal[as.character(s)])
}
g = graph_from_edgelist(edges, directed = TRUE)
lay = t(sapply(1:n, function(i) { ang = pi / 2 - 2 * pi * (i - 1) / n; c(cos(ang), sin(ang)) }))

pdf("Paley7.pdf", width = 6.5, height = 6.6)
par(mar = c(0.5, 0.4, 0.4, 0.4), xpd = NA)
plot(g, layout = lay, ylim = c(-1.52, 1.03),
     vertex.color = "orange", vertex.label = 0:(n - 1),
     vertex.label.color = "navy", vertex.label.cex = 1.5, vertex.size = 20,
     edge.color = ecol, edge.width = 1.7, edge.arrow.size = 0.5, edge.curved = 0)
legend(x = 0, y = -1.30, xjust = 0.5, yjust = 1, horiz = TRUE,
       legend = paste0("s = ", names(pal)), col = pal, lwd = 2.6,
       bty = "n", cex = 1.05, seg.len = 1.4,
       title = expression("arc class:  (v - u) mod 7 = s"))
dev.off()
cat("Paley7.pdf written\n")
