# reg11_alphastar.R — EXACT rational alpha* for all 1223 regular tournaments on 11 vertices.
#
# Regular (Eulerian) but NOT vertex-transitive in general, so we MUST use the general weighted-MAS
# oracle (full 2^n DP, no fix-vertex-0). The fix-vertex-0 shortcut is UNWEIGHTED-only: for an
# Eulerian tournament, rotating the first vertex to the end trades its (n-1)/2 forward out-arcs
# for its (n-1)/2 in-arcs, so the forward COUNT is unchanged (any cyclic rotation of a max order
# is max) -> can fix vertex 0 in the *unweighted* MAS DP. With weights that trade is
# sum_j W[v0][j] vs sum_j W[j][v0], which do NOT cancel -> invalid for the weighted alpha* oracle.
#
# Pipeline per tournament: float cutting-plane (asp_full) converges a cut set; exact rational LP
# over that cut set via rcdd/GMP (asp_exact); then CERTIFY by re-running the oracle at the exact
# optimum weighting (add any violated cut and re-solve) so the returned rational is provably alpha*.
#
# Goal: distribution of alpha* over the 1223, and test Conjecture A at threshold (k+1)/(2k)=2/3 for
# k=3: "3-realizable => alpha* >= 2/3" is the (proven) necessary direction; the conjecture claims
# sufficiency (alpha* >= 2/3 => 3-realizable). A tournament with alpha* >= 2/3 that is NOT
# 3-realizable would refute it; one with alpha* < 2/3 is automatically non-3-realizable (consistent).

suppressMessages({ library(lpSolve); library(rcdd); library(gmp) })
source("../common/alpha_star.R")   # maxweight_order: general weighted-MAS DP (no fix-0)

# ---- float cutting plane on adjacency D (D[i,j]=1 => arc i->j); returns the converged cut set ----
asp_full <- function(D, tol = 1e-9) {
  n <- nrow(D); a <- which(D == 1L, arr.ind = TRUE); af <- a[, 1]; at <- a[, 2]; E <- length(af)
  Wm  <- function(y) { W <- matrix(0, n, n); W[cbind(af, at)] <- y; W }
  con <- function(o) { p <- integer(n); p[o] <- 1:n; as.numeric(p[af] < p[at]) }
  cuts <- matrix(con(1:n), nrow = 1)
  repeat {
    K <- nrow(cuts); ob <- c(rep(0, E), 1); cm <- rbind(c(rep(1, E), 0), cbind(cuts, rep(-1, K)))
    s <- lp("min", ob, cm, c("=", rep("<=", K)), c(1, rep(0, K)))
    t <- s$solution[E + 1]; y <- s$solution[1:E]
    mo <- maxweight_order(Wm(y))
    if (mo$value <= t + tol) return(list(alpha = t, cuts = cuts, E = E, af = af, at = at, n = n))
    cuts <- rbind(cuts, con(mo$order))
  }
}

# ---- exact rational LP over a cut set (rcdd/GMP) ----
asp_exact <- function(cuts, E) {
  K <- nrow(cuts)
  A_cut <- cbind(cuts, matrix(-1, K, 1))            # (cut . y) - t <= 0
  A_nn  <- cbind(-diag(E), matrix(0, E, 1))         # -y_j <= 0
  a1 <- rbind(A_cut, A_nn); b1 <- rep(0, K + E)
  a2 <- matrix(c(rep(1, E), 0), nrow = 1); b2 <- 1  # sum y = 1
  hrep <- makeH(d2q(a1), d2q(b1), d2q(a2), d2q(b2))
  objg <- d2q(c(rep(0, E), 1))                      # minimize t
  out  <- lpcdd(hrep, objg, minimize = TRUE)
  out
}

# ---- certified exact alpha* for one tournament ----
exact_alpha <- function(D, tol = 1e-9) {
  fit <- asp_full(D, tol); af <- fit$af; at <- fit$at; n <- fit$n; E <- fit$E
  cuts <- fit$cuts
  repeat {
    ex <- asp_exact(cuts, E)
    if (ex$solution.type != "Optimal") stop("rcdd non-optimal: ", ex$solution.type)
    yq <- ex$primal.solution[1:E]                   # exact rational weighting (q strings)
    yd <- q2d(yq)
    W  <- matrix(0, n, n); W[cbind(af, at)] <- yd
    mo <- maxweight_order(W)
    ad <- q2d(ex$optimal.value)
    if (mo$value <= ad + 1e-7) {                     # no order beats exact alpha* => certified
      return(list(alpha_q = as.character(ex$optimal.value), alpha_d = ad,
                  gap = mo$value - ad, ncuts = nrow(cuts)))
    }
    p <- integer(n); p[mo$order] <- 1:n              # add the violated cut, re-solve exactly
    cuts <- rbind(cuts, as.numeric(p[af] < p[at]))
  }
}

# ------------------------------------------------------------------------------------------------
args <- commandArgs(trailingOnly = TRUE)
NMAX <- if (length(args) >= 1) as.integer(args[1]) else NA_integer_   # process first NMAX (NA=all)
OUT  <- if (length(args) >= 2) args[2] else "reg11_alpha_results.rds"

e <- new.env(); load("../data/regulartournaments11.RData", envir = e); G <- e$allGraphs
N <- length(G); if (!is.na(NMAX)) N <- min(N, NMAX)
cat(sprintf("regular tournaments on 11 vertices: processing %d of %d\n", N, length(G)))

alpha_q <- character(N); alpha_d <- numeric(N); gap <- numeric(N); ncuts <- integer(N)
t0 <- Sys.time()
for (i in seq_len(N)) {
  r <- exact_alpha(G[[i]])
  alpha_q[i] <- r$alpha_q; alpha_d[i] <- r$alpha_d; gap[i] <- r$gap; ncuts[i] <- r$ncuts
  if (i %% 50 == 0 || i == N) {
    dt <- as.numeric(Sys.time() - t0, units = "secs")
    cat(sprintf("  %4d/%d  %.1fs  (%.3fs/tourn)  min=%.6f max=%.6f maxgap=%.1e\n",
                i, N, dt, dt / i, min(alpha_d[1:i]), max(alpha_d[1:i]), max(gap[1:i])))
    saveRDS(list(alpha_q = alpha_q[1:i], alpha_d = alpha_d[1:i], gap = gap[1:i],
                 ncuts = ncuts[1:i], done = i), OUT)
    flush.console()
  }
}

# ------------------------------ report -----------------------------------------------------------
two3 <- as.bigq(2L, 3L)
aq <- as.bigq(alpha_q)
lt <- sum(aq <  two3); eq <- sum(aq == two3); gt <- sum(aq >  two3)
cat("\n================= alpha* over the", N, "regular tournaments on 11 vertices =================\n")
cat(sprintf("min alpha* = %s (%.6f)   max alpha* = %s (%.6f)\n",
            alpha_q[which.min(alpha_d)], min(alpha_d), alpha_q[which.max(alpha_d)], max(alpha_d)))
cat(sprintf("max verification gap = %.2e  (all certified: %s)\n", max(gap), all(gap < 1e-7)))
cat(sprintf("\nConjecture A threshold 2/3 (= %.6f):\n", 2/3))
cat(sprintf("  alpha* <  2/3 : %4d   (provably NOT 3-realizable — consistent with conjecture)\n", lt))
cat(sprintf("  alpha* == 2/3 : %4d   (on the boundary)\n", eq))
cat(sprintf("  alpha* >  2/3 : %4d   (candidates: refute conjecture iff any is NOT 3-realizable)\n", gt))

cat("\ndistribution of exact alpha* (value : count):\n")
tab <- sort(table(alpha_q), decreasing = TRUE)
uq  <- as.bigq(names(tab)); ord <- order(as.double(uq))
for (k in ord) cat(sprintf("  %-10s (%.6f) : %d\n", names(tab)[k], as.double(uq[k]), tab[k]))
saveRDS(list(alpha_q = alpha_q, alpha_d = alpha_d, gap = gap, ncuts = ncuts, done = N), OUT)
cat("\nsaved:", OUT, "\n")
