#!/usr/bin/env Rscript
# ============================================================================
# Exact realizability LP value alpha*(T) via cutting-plane (row/column generation)
# with a WEIGHTED max-acyclic-subgraph DP oracle -- NO permutation enumeration.
#
#   alpha*(T) = min over edge-distributions y   max over linear orders pi
#                 sum_{pairs consistent with T under pi} y_pair
#             = the realizability LP optimum (max-min edge support over voter mixtures).
#
# Certificate:  alpha*(T) < (k+1)/(2k+1)  =>  T is not (2k+1)-realizable.
#   3 voters: threshold 2/3 ;  5 voters: threshold 3/5.
# The optimal y is the fractional obstruction (edge-obstruction weights), free on the side.
#
# Oracle = the same subset DP as min-FAS, but maximizing a weighted forward-arc sum,
# so memory is O(2^n) (~KB) and it scales to n~16+ without ever listing n! orders.
# ============================================================================
suppressMessages(library(lpSolve))

# Weighted max-acyclic-subgraph: arc-weight matrix W (W[u,v] = weight of arc u->v, 0 if absent).
# Returns the linear order maximizing total forward-arc weight, and that value.
maxweight_order <- function(W, tilim = Inf) {             # tilim accepted but ignored: the DP is always exact
  n <- nrow(W); vbit <- bitwShiftL(1L, 0:(n - 1)); FULL <- bitwShiftL(1L, n) - 1L
  f <- rep(-Inf, FULL + 1L); f[1L] <- 0; par <- integer(FULL + 1L)
  for (S in 0:FULL) {
    fS <- f[S + 1L]; if (!is.finite(fS)) next
    inS <- bitwAnd(S, vbit) != 0L; av <- which(!inS)        # available vertices to append next
    contrib <- as.vector(crossprod(W, as.numeric(inS)))[av] # contrib[v] = sum_{u in S} W[u,v]
    tgt <- bitwOr(S, vbit[av]) + 1L; val <- fS + contrib    # distinct tgt within this S -> no intra-collision
    upd <- val > f[tgt]
    if (any(upd)) { f[tgt[upd]] <- val[upd]; par[tgt[upd]] <- av[upd] }
  }
  ord <- integer(n); S <- FULL
  for (k in n:1) { v <- par[S + 1L]; ord[k] <- v; S <- bitwAnd(S, bitwXor(FULL, vbit[v])) }
  list(value = f[FULL + 1L], order = ord)                   # ord[1] = earliest position
}

# alpha*(A) for tournament A (A[i,j]=1 means i->j).
# stop_above: if the increasing lower bound t ever exceeds this, return early with exact=FALSE
# (alpha* >= t > stop_above is enough to rule out a counterexample below stop_above).
# tilim: per-oracle-call time cap (s) for an inexact oracle. Any linear order is a valid cut, so a
#   time-limited (sub-optimal) oracle still drives the lower bound t upward; the oracle returns
#   $bound (an upper bound on its own optimum), and we escalate a SINGLE call to an exact solve only
#   when its incumbent can't beat t yet optimality is unproven. tilim=Inf => always exact (default).
alpha_star <- function(A, tol = 1e-7, max_iter = 5000, stop_above = Inf, oracle = maxweight_order, trace = 0L, tilim = Inf) {
  n <- nrow(A); pairs <- t(combn(n, 2)); C <- nrow(pairs)
  af <- integer(C); at <- integer(C)                        # tournament arc direction per pair
  for (e in 1:C) { i <- pairs[e, 1]; j <- pairs[e, 2]
    if (A[i, j] == 1L) { af[e] <- i; at[e] <- j } else { af[e] <- j; at[e] <- i } }
  consistency <- function(ord) { pos <- integer(n); pos[ord] <- 1:n; as.numeric(pos[af] < pos[at]) }
  Wmat <- function(y) { W <- matrix(0, n, n); W[cbind(af, at)] <- y; W }

  cuts <- matrix(consistency(1:n), nrow = 1)                # seed with identity order
  repeat {
    K <- nrow(cuts)
    obj <- c(rep(0, C), 1)                                  # vars y_1..y_C, t ; minimize t
    con <- rbind(c(rep(1, C), 0), cbind(cuts, rep(-1, K)))  # sum y = 1 ; cut.y - t <= 0
    sol <- lp("min", obj, con, c("=", rep("<=", K)), c(1, rep(0, K)))
    y <- sol$solution[1:C]; t <- sol$solution[C + 1]
    if (t > stop_above + tol)                              # alpha* >= t > cutoff: not a sub-cutoff counterexample
      return(list(alpha = t, exact = FALSE, y = y, pairs = pairs, af = af, at = at, iters = K))
    mo <- oracle(Wmat(y), tilim = tilim)                   # any returned order is a valid cut (need not be optimal)
    bnd <- if (is.null(mo$bound)) mo$value else mo$bound    # upper bound on the true oracle optimum (== value if exact)
    if (mo$value <= t + tol && bnd > t + tol) {            # incumbent can't beat t but optimality unproven -> escalate
      mo <- oracle(Wmat(y), tilim = Inf)                   # exact solve: yields a violated cut, or certifies alpha* = t
      bnd <- if (is.null(mo$bound)) mo$value else mo$bound }
    if (trace > 0L && K %% trace == 0L) {
      cat(sprintf("  [cut %d] t=%.7f oracle=%.7f bound=%.7f gap=%.2e\n", K, t, mo$value, bnd, bnd - t)); flush.console() }
    if (bnd <= t + tol)                                    # no order exceeds t  =>  alpha* = t exactly
      return(list(alpha = t, exact = TRUE, y = y, pairs = pairs, af = af, at = at, iters = K))
    cuts <- rbind(cuts, consistency(mo$order))
    if (nrow(cuts) > max_iter) stop("alpha_star: cut limit reached")
  }
}
