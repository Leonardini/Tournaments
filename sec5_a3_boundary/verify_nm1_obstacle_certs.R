# SOLVER-FREE static certification of the non-margin-1 (margin-1-only) n=9 obstacles.
# Depends on gmp ONLY (exact rationals) -- no LP solver, no cddlib, no CPLEX in the trust path.
# Each certificate carries a primal distribution x over orders and a SIGNED dual weighting y.
#   primal x : Sum x = 1, x >= 0, EXACT uniform coverage p/q on every arc  => alpha^= >= p/q
#              (signed-y lower bound needs EQUALITY: Sum_e y_e cov_e = (p/q) Sum y_e = p/q).
#   signed y : Sum y = 1, exact signed Held-Karp weighted-MAS(y) <= p/q     => alpha^= <= p/q
#   together alpha^= = p/q, and we assert p/q < 2/3.
suppressMessages(library(gmp))
CERTS <- commandArgs(trailingOnly = TRUE)[1]; if (is.na(CERTS)) CERTS <- "n9_nm1_obstacle_certs.rds"
C <- readRDS(CERTS)

# exact SIGNED Held-Karp weighted-MAS (init -inf via -1000; negative arc weights allowed)
wmas <- function(af, at, y, n) {
  inv <- vector("list", n); for (k in seq_along(af)) inv[[at[k]]] <- c(inv[[at[k]]], k)
  pw <- as.integer(2^(0:(n - 1))); g <- as.bigq(rep(0L, 2^n))
  for (m in 1:(2^n - 1)) { b <- as.bigq(-1000L)
    for (v in which(bitwAnd(m, pw) > 0)) { p <- m - pw[v]; a <- as.bigq(0L)
      for (k in inv[[v]]) if (bitwAnd(p, pw[af[k]]) > 0) a <- a + y[k]
      val <- g[p + 1] + a; if (val > b) b <- val }
    g[m + 1] <- b }
  g[2^n]
}

ok <- 0; TWO3 <- as.bigq(2L, 3L)
for (cc in C) {
  pq <- as.bigq(cc$alpha); x <- as.bigq(cc$x); y <- as.bigq(cc$y); E <- length(cc$af); cuts <- cc$cuts
  P  <- (sum(x) == 1L) && all(x >= 0) &&
        all(sapply(1:E, function(ee) sum(x[cuts[, ee] == 1]) == pq))   # EXACT coverage = p/q
  Dl <- (sum(y) == 1L) && (wmas(cc$af, cc$at, y, cc$n) <= pq)          # signed => alpha <= p/q
  below <- (pq < TWO3)
  if (P && Dl && below) ok <- ok + 1 else
    cat(sprintf("  FAIL key=%s alpha=%s  primal=%s dual=%s below2/3=%s\n",
                if (!is.null(cc$key)) substr(cc$key, 1, 12) else "?", cc$alpha, P, Dl, below))
}
vals <- sort(unique(sapply(C, function(z) z$alpha)))
cat(sprintf("STATIC (gmp-only) certification: %d/%d non-margin-1 obstacles, exact alpha^= = p/q < 2/3 via primal+signed-dual\n",
            ok, length(C)))
cat(sprintf("distinct alpha^= values (%d): %s\n", length(vals), paste(vals, collapse = " ")))
