#!/usr/bin/env Rscript
# EXACT solver-free certification of each DISTINCT non-margin-1 obstacle.
# Input : a catalogue rds = list of obstacles, each with $AF,$AT (arc endpoints on the
#         non-isolated vertex set relabelled 1..n) OR a canonical adjacency $D.
# Output: minted certs (gmp-checkable): per obstacle {af,at,n,cuts,x,y,alpha,ok,below}.
#   primal x : Sum x = 1, x >= 0, EXACT uniform coverage p/q on every arc  => alpha^= >= p/q
#   signed y : Sum y = 1, exact signed Held-Karp weighted-MAS(y) <= p/q    => alpha^= <= p/q
#   together alpha^= = p/q, and we assert p/q < 2/3.
suppressMessages({ library(igraph); library(rcdd); library(gmp) })
args <- commandArgs(trailingOnly = TRUE)
INRDS  <- if (length(args) >= 1) args[1] else "../data/n9_nm1_obstacle_catalog.rds"
OUTRDS <- if (length(args) >= 2) args[2] else "n9_nm1_obstacle_certs.rds"

con <- function(o, af, at, n) { p <- integer(n); p[o] <- 1:n; as.numeric(p[af] < p[at]) }
ewm <- function(af, at, yq, n) {   # exact signed Held-Karp weighted-MAS + order
  inv <- vector("list", n); for (k in seq_along(af)) inv[[at[k]]] <- c(inv[[at[k]]], k)
  pw <- as.integer(2^(0:(n - 1))); g <- as.bigq(rep(0L, 2^n)); ch <- integer(2^n)
  for (m in 1:(2^n - 1)) { b <- as.bigq(-1000L); bv <- 0L
    for (v in which(bitwAnd(m, pw) > 0)) { p <- m - pw[v]; ad <- as.bigq(0L)
      for (k in inv[[v]]) if (bitwAnd(p, pw[af[k]]) > 0) ad <- ad + yq[k]
      val <- g[p + 1] + ad; if (val > b) { b <- val; bv <- v } }
    g[m + 1] <- b; ch[m + 1] <- bv }
  mm <- 2^n - 1; ord <- integer(n); q <- n
  while (mm > 0) { v <- ch[mm + 1]; ord[q] <- v; q <- q - 1; mm <- mm - pw[v] }
  list(value = g[2^n], order = ord)
}
ewm_f <- function(af, at, y, n) {   # float signed Held-Karp weighted-MAS + order (fast separation)
  inv <- vector("list", n); for (k in seq_along(af)) inv[[at[k]]] <- c(inv[[at[k]]], k)
  pw <- as.integer(2^(0:(n - 1))); g <- rep(-Inf, 2^n); g[1] <- 0; ch <- integer(2^n)
  for (m in 1:(2^n - 1)) { b <- -Inf; bv <- 0L
    for (v in which(bitwAnd(m, pw) > 0)) { p <- m - pw[v]; ad <- 0
      for (k in inv[[v]]) if (bitwAnd(p, pw[af[k]]) > 0) ad <- ad + y[k]
      val <- g[p + 1] + ad; if (val > b) { b <- val; bv <- v } }
    g[m + 1] <- b; ch[m + 1] <- bv }
  mm <- 2^n - 1; ord <- integer(n); q <- n
  while (mm > 0) { v <- ch[mm + 1]; ord[q] <- v; q <- q - 1; mm <- mm - pw[v] }
  list(value = g[2^n], order = ord)
}

# exact certificate on arc set (af,at) over n vertices (all non-isolated)
cert <- function(af, at, n) {
  E <- length(af)
  cuts <- rbind(con(1:n, af, at, n), con(n:1, af, at, n))
  set.seed(7); cuts <- rbind(cuts, do.call(rbind, lapply(1:40, function(.) con(sample(n), af, at, n))))
  repeat {   # exact LP (rcdd) with FLOAT Held-Karp separation, EXACT confirmation on convergence
    K <- nrow(cuts)
    ex <- lpcdd(makeH(d2q(cbind(cuts, matrix(-1, K, 1))), d2q(rep(0, K)),
                      d2q(matrix(c(rep(1, E), 0), nrow = 1)), d2q(1)),
                d2q(c(rep(0, E), 1)), minimize = TRUE)
    if (ex$solution.type != "Optimal") { cuts <- rbind(cuts, do.call(rbind, lapply(1:40, function(.) con(sample(n), af, at, n)))); next }
    astar <- as.bigq(ex$optimal.value); yq <- as.bigq(ex$primal.solution[1:E])
    mo <- ewm_f(af, at, as.numeric(yq), n)
    if (mo$value > as.numeric(astar) + 1e-9) { cuts <- rbind(cuts, con(mo$order, af, at, n)); next }
    moE <- ewm(af, at, yq, n)                       # exact confirmation
    if (moE$value <= astar) break
    cuts <- rbind(cuts, con(moE$order, af, at, n))
  }
  # exact primal: max t s.t. Sum x = 1, x>=0, coverage_e - t = 0 for all arcs
  Kc <- nrow(cuts)
  exP <- lpcdd(makeH(d2q(cbind(-diag(Kc), rep(0, Kc))), d2q(rep(0, Kc)),
                     d2q(rbind(matrix(c(rep(1, Kc), 0), nrow = 1), cbind(t(cuts), rep(-1, E)))),
                     d2q(c(1, rep(0, E)))),
               d2q(c(rep(0, Kc), -1)), minimize = TRUE)
  x <- as.bigq(exP$primal.solution[1:Kc]); keep <- which(x != 0)
  P  <- (sum(x) == 1L) && all(x >= 0) && all(sapply(1:E, function(ee) sum(x[cuts[, ee] == 1]) == astar))
  Dl <- (sum(yq) == 1L) && (ewm(af, at, yq, n)$value <= astar)
  list(af = af, at = at, n = n, cuts = cuts[keep, , drop = FALSE], x = as.character(x[keep]),
       y = as.character(yq), alpha = as.character(astar), ok = P && Dl,
       below = (astar < as.bigq(2L, 3L)))
}

# decode an obstacle entry -> (af,at,n) on non-isolated vertices
decode <- function(o) {
  if (!is.null(o$D)) { D <- o$D; a <- which(D == 1, arr.ind = TRUE); af <- a[, 1]; at <- a[, 2] }
  else { af <- o$AF; at <- o$AT }
  vs <- sort(unique(c(af, at))); rl <- integer(max(vs)); rl[vs] <- seq_along(vs)
  list(af = rl[af], at = rl[at], n = length(vs))
}

cat_key <- function(af, at, n) {  # canonical iso key for dedup safety
  g <- make_graph(edges = as.vector(rbind(af, at)), n = n, directed = TRUE)
  paste(as.integer(as_adjacency_matrix(permute(g, canonical_permutation(g)$labeling), sparse = FALSE)), collapse = "")
}

IN <- readRDS(INRDS); if (!is.null(IN$distinct)) IN <- IN$distinct   # catalogue -> obstacle list
cat(sprintf("certifying %d distinct obstacles from %s\n", length(IN), INRDS)); flush.console()
C <- list(); ok <- 0; bel <- 0; t0 <- Sys.time()
for (j in seq_along(IN)) {
  d <- decode(IN[[j]]); r <- cert(d$af, d$at, d$n)
  r$key <- cat_key(d$af, d$at, d$n)
  if (!is.null(IN[[j]]$key)) r$src_key <- IN[[j]]$key
  C[[j]] <- r; ok <- ok + r$ok; bel <- bel + r$below
  cat(sprintf("  [%d/%d] alpha=%-7s ok=%s below=%s n=%d E=%d (%.0fs)\n",
              j, length(IN), r$alpha, r$ok, r$below, r$n, length(r$af), as.numeric(Sys.time() - t0, units = "secs"))); flush.console()
  saveRDS(C, OUTRDS)
}
vals <- sort(unique(sapply(C, function(z) z$alpha)))
cat(sprintf("\n== CERTIFIED %d/%d exact primal+dual ; all alpha^=<2/3 : %d/%d ==\n distinct alpha values: %s\n",
            ok, length(C), bel, length(C), paste(vals, collapse = " ")))
