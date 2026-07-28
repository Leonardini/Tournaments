# inmask_alpha.R <inmasksfile> — exact rational alpha* for each tournament in an inmasks file
# (one per line: inm[v] = bitmask of in-neighbours u of v, arc u->v; n = #tokens). Uses the general
# (no fix-0) oracle + rcdd/GMP exact LP + oracle re-verification, identical to reg11_alphastar.R.
suppressMessages({ library(lpSolve); library(rcdd); library(gmp) })
source("ObsoleteSourceFiles/alpha_star.R")   # maxweight_order (general DP)
asp_full <- function(D, tol = 1e-9) {
  n <- nrow(D); a <- which(D == 1L, arr.ind = TRUE); af <- a[, 1]; at <- a[, 2]; E <- length(af)
  Wm  <- function(y) { W <- matrix(0, n, n); W[cbind(af, at)] <- y; W }
  con <- function(o) { p <- integer(n); p[o] <- 1:n; as.numeric(p[af] < p[at]) }
  cuts <- matrix(con(1:n), nrow = 1)
  repeat {
    K <- nrow(cuts); ob <- c(rep(0, E), 1); cm <- rbind(c(rep(1, E), 0), cbind(cuts, rep(-1, K)))
    s <- lp("min", ob, cm, c("=", rep("<=", K)), c(1, rep(0, K)))
    t <- s$solution[E + 1]; y <- s$solution[1:E]; mo <- maxweight_order(Wm(y))
    if (mo$value <= t + tol) return(list(cuts = cuts, E = E, af = af, at = at, n = n))
    cuts <- rbind(cuts, con(mo$order))
  }
}
asp_exact <- function(cuts, E) { K <- nrow(cuts)
  a1 <- rbind(cbind(cuts, matrix(-1, K, 1)), cbind(-diag(E), matrix(0, E, 1))); b1 <- rep(0, K + E)
  hrep <- makeH(d2q(a1), d2q(b1), d2q(matrix(c(rep(1, E), 0), nrow = 1)), d2q(1))
  lpcdd(hrep, d2q(c(rep(0, E), 1)), minimize = TRUE) }
ea <- function(D) { f <- asp_full(D); cuts <- f$cuts
  repeat { ex <- asp_exact(cuts, f$E); yd <- q2d(ex$primal.solution[1:f$E])
    W <- matrix(0, f$n, f$n); W[cbind(f$af, f$at)] <- yd; mo <- maxweight_order(W); ad <- q2d(ex$optimal.value)
    if (mo$value <= ad + 1e-7) return(ex$optimal.value)
    p <- integer(f$n); p[mo$order] <- 1:f$n; cuts <- rbind(cuts, as.numeric(p[f$af] < p[f$at])) } }
decode <- function(toks) { inm <- as.integer(toks); n <- length(inm); A <- matrix(0L, n, n)
  for (v in 1:n) for (u in 1:n) if (bitwAnd(bitwShiftR(inm[v], u - 1L), 1L) == 1L) A[u, v] <- 1L; A }

f <- commandArgs(trailingOnly = TRUE)[1]
lines <- strsplit(trimws(readLines(f)), "[[:space:]]+"); lines <- lines[lengths(lines) > 0]
two3 <- as.bigq(2L, 3L)
for (i in seq_along(lines)) { A <- decode(lines[[i]]); n <- nrow(A)
  masC <- as.bigq(max(sapply(1:1, function(z) maxweight_order(matrix(as.numeric(A), n, n))$value)), n * (n - 1) / 2)
  aq <- as.bigq(ea(A))
  cat(sprintf("%s line %d: n=%d  alpha* = %s (%.5f)  MAS/C = %s (%.5f)  [alpha* %s 2/3]\n",
    basename(f), i, n, as.character(aq), as.double(aq), as.character(masC), as.double(masC),
    if (aq > two3) ">" else if (aq == two3) "=" else "<")) }
