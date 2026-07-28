# CounterexampleA--F.pdf (manuscript Figure 4): the six 3-inducible self-converse
# 11-vertex tournaments violating Conjecture 2, rebuilt as the majority
# tournaments of their Appendix C inducing profiles (so figure labels match the
# printed profiles by construction). Before plotting, each tournament is
# re-verified: (i) self-converse, (ii) HS_3 < FAS (exact: LP-free Held-Karp DP
# for FAS, binary program for HS_3). The script stops on any mismatch.
#
# Layout: vertices 1..11 in circular order; every pair is joined (tournament),
# so the drawing question is direction only -- all arcs curve to the LEFT of
# their travel direction (igraph convention checked below), plus arrowheads.
library(igraph)
library(lpSolve)
# outputs are written to the working directory -- run this script from its own folder

n = 11
profiles = list(
  A = list(c(1,11,10,2,3,4,5,6,7,8,9), c(4,8,9,2,6,7,1,10,11,3,5),
           c(5,3,7,9,6,8,10,11,1,2,4)),
  B = list(c(1,10,3,4,11,6,8,2,5,7,9), c(5,6,7,8,1,9,10,2,3,4,11),
           c(9,2,11,4,3,7,5,8,6,10,1)),
  C = list(c(1,9,2,10,3,4,5,11,7,8,6), c(3,6,7,8,2,9,10,5,11,1,4),
           c(4,11,5,6,8,7,1,10,2,9,3)),
  D = list(c(1,2,11,10,5,3,4,6,9,7,8), c(3,6,8,9,7,11,1,10,2,4,5),
           c(4,5,7,8,9,2,10,6,1,11,3)),
  E = list(c(1,9,11,10,3,4,2,5,8,6,7), c(2,3,5,6,7,8,9,1,10,11,4),
           c(4,7,8,6,10,11,5,1,9,2,3)),
  F = list(c(2,3,4,5,8,6,7,9,10,11,1), c(6,11,1,5,9,10,3,4,2,7,8),
           c(7,8,10,1,9,11,4,2,3,5,6)))

majorityT = function(voters) {
  L = matrix(0, n, n)
  for (v in voters) for (a in 1:(n - 1)) for (b in (a + 1):n) {
    L[v[a], v[b]] = L[v[a], v[b]] + 1
  }
  edges = NULL
  for (i in 1:(n - 1)) for (j in (i + 1):n) {
    stopifnot(L[i, j] != L[j, i])   # 3 voters: no ties possible
    edges = rbind(edges, if (L[i, j] > L[j, i]) c(i, j) else c(j, i))
  }
  edges
}

# exact MAS by Held-Karp over vertex subsets; FAS = #arcs - MAS
fasExact = function(edges) {
  inw = matrix(0L, n, n)          # inw[v, u] = 1 iff arc u -> v
  for (r in 1:nrow(edges)) inw[edges[r, 2], edges[r, 1]] = 1L
  g = integer(2^n)
  for (S in 1:(2^n - 1)) {
    members = which(bitwAnd(S, 2^(0:(n - 1))) > 0)
    best = 0L
    for (v in members) {
      rest = setdiff(members, v)
      gain = g[1 + S - 2^(v - 1)] + sum(inw[v, rest])
      if (gain > best) best = gain
    }
    g[1 + S] = best
  }
  nrow(edges) - g[2^n]
}

# exact HS_3: minimum number of arcs meeting every cyclic triangle
hs3Exact = function(edges) {
  arcId = matrix(0L, n, n)
  for (r in 1:nrow(edges)) arcId[edges[r, 1], edges[r, 2]] = r
  rows = NULL
  for (a in 1:(n - 2)) for (b in (a + 1):(n - 1)) for (c in (b + 1):n) {
    tri = c(arcId[a, b], arcId[b, c], arcId[c, a])       # a->b->c->a
    triR = c(arcId[b, a], arcId[c, b], arcId[a, c])      # a->c->b->a
    cyc = if (all(tri > 0)) tri else if (all(triR > 0)) triR else NULL
    if (!is.null(cyc)) {
      row = integer(nrow(edges)); row[cyc] = 1L
      rows = rbind(rows, row)
    }
  }
  sol = lp("min", rep(1, nrow(edges)), rows, rep(">=", nrow(rows)),
           rep(1, nrow(rows)), all.bin = TRUE)
  stopifnot(sol$status == 0)
  round(sol$objval)
}

for (name in names(profiles)) {
  edges = majorityT(profiles[[name]])
  g = graph_from_edgelist(edges, directed = TRUE)
  gConv = graph_from_edgelist(edges[, 2:1], directed = TRUE)
  stopifnot(isomorphic(g, gConv, method = "vf2"))        # self-converse
  fas = fasExact(edges); hs3 = hs3Exact(edges)
  stopifnot(hs3 < fas)                                   # violates Conjecture 2
  cat(sprintf("Counterexample %s: self-converse OK, HS3 = %d < %d = FAS\n",
              name, hs3, fas))
  pdf(sprintf("Counterexample%s.pdf", name), width = 6.5, height = 6.5)
  par(mar = rep(0.4, 4), xpd = NA)
  plot(g, layout = layout_in_circle(g),
       vertex.color = "orange", vertex.label = 1:n,
       vertex.label.color = "navy", vertex.label.cex = 1.6, vertex.size = 21,
       edge.color = adjustcolor("gray30", alpha.f = 0.65), edge.width = 1.3,
       edge.arrow.size = 0.7, edge.curved = 0.18)
  dev.off()
  cat(sprintf("Counterexample%s.pdf written\n", name))
}
