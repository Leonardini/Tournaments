#!/usr/bin/env Rscript
# COMPLETE census of non-margin-1 (margin-1-only) n=9 obstacles.
# Obstacle = support of an EXTREME optimal SIGNED dual (vertex of the optimal-dual face).
# Method (exact, matches the shipped margin-1 pipeline with y>=0 dropped):
#   alpha^=(T) = min over signed y (Sum y = 1) of weighted-MAS(y)   [< 2/3].
#   Optimal-dual face P* = { y : Sum y = 1, f^sigma . y <= alpha* for every order sigma }.
#   P* is a bounded polytope (linear-ordering polytope is full-dim => recession cone {0});
#   a box |y|<=B regularises the partial (column-generated) face and is verified non-binding.
#   Reduce to FLEX arcs (lo<hi over P*); CORE arcs are fixed; scdd vertex-enumerates the
#   low-dim flex polytope EXACTLY; vertex-witness saturation adds any order a corner violates
#   until every vertex is a true optimal dual.  Each vertex's support = one extreme obstacle.
suppressMessages({ library(igraph); library(rcdd); library(gmp) })
DATA <- Sys.getenv("NM1_DATA", "../data")
CE <- readRDS(file.path(DATA, "n9_margin1only_tournaments.rds"))   # 254 margin-1-only n=9 tournaments (adjacency)
args <- commandArgs(trailingOnly = TRUE)
RANGE <- if (length(args) >= 1) eval(parse(text = args[1])) else 1:length(CE)
OUT   <- if (length(args) >= 2) args[2] else "nm1_face_out.rds"
B <- 8L; TOL <- 1e-9

con <- function(o, af, at, n) { p <- integer(n); p[o] <- 1:n; as.numeric(p[af] < p[at]) }
# float signed Held-Karp weighted-MAS + witnessing order (fast separation oracle)
ewm_f <- function(af, at, y, n) {
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
LRS_BIN <- Sys.getenv("LRS_BIN", path.expand("~/Downloads/DownloadedSoftware/lrslib-073/lrs"))
# Exact vertex enumeration of the signed flex polytope via lrs (reverse search, exact rational):
#   y_i <= B, -y_i <= B, (q G_flex) y <= rhs, sum y = sflex.  Box => bounded => no rays.
# Returns a character matrix (rows = vertices, cols = m flex coords, exact q).
flex_vertices_lrs <- function(Gf, rhs, sflex, m, B) {
  rows <- vector("list", 2 * m + nrow(Gf) + 1L)
  for (i in 1:m) { r <- as.bigq(integer(m + 1)); r[1] <- as.bigq(B);  r[1 + i] <- as.bigq(-1L); rows[[i]] <- r }        # B - y_i >= 0
  for (i in 1:m) { r <- as.bigq(integer(m + 1)); r[1] <- as.bigq(B);  r[1 + i] <- as.bigq(1L);  rows[[m + i]] <- r }    # B + y_i >= 0
  for (g in 1:nrow(Gf)) rows[[2 * m + g]] <- c(rhs[g], -Gf[g, ])                                                        # rhs_g - Gf_g.y >= 0
  rows[[2 * m + nrow(Gf) + 1L]] <- c(-sflex, rep(as.bigq(1L), m))                                                       # sum y = sflex
  lin_row <- length(rows)
  body <- sapply(rows, function(r) paste(as.character(r), collapse = " "))
  ine <- c("flex", "H-representation", sprintf("linearity 1 %d", lin_row),
           "begin", sprintf("%d %d rational", length(rows), m + 1L), body, "end")
  if (Sys.getenv("VERB") == "1") cat(sprintf("    [lrs] m=%d rows=%d\n", m, length(rows)), file = stderr())
  out <- NULL
  for (attempt in 1:4) {                               # lrs 7.3 can segfault non-deterministically -> retry
    f <- tempfile(fileext = ".ine"); writeLines(ine, f)
    o <- system2(LRS_BIN, f, stdout = TRUE, stderr = FALSE); unlink(f)
    if (length(which(o == "begin")) && length(which(o == "end"))) { out <- o; break }
  }
  if (is.null(out)) return(NULL)                       # caller falls back to scdd
  b <- which(out == "begin"); e <- which(out == "end")
  vlines <- out[(b[1] + 2L):(e[1] - 1L)]
  verts <- list()
  for (ln in vlines) { tok <- strsplit(trimws(ln), "[[:space:]]+")[[1]]
    if (length(tok) != m + 1L || tok[1] != "1") next   # 1 = vertex (0 = ray, none: box-bounded); exactly m coords
    verts[[length(verts) + 1L]] <- tok[-1] }
  if (!length(verts)) return(NULL)
  do.call(rbind, verts)
}
# scdd fallback (rcdd double description) on the SAME order-bounded flex polytope.
flex_vertices_scdd <- function(Gf, rhs, sflex, m, B) {
  ord_rows <- cbind("0", as.character(rhs), matrix(as.character(-Gf), nrow = nrow(Gf)))
  eq_row   <- cbind("1", as.character(sflex), matrix(as.character(-as.bigq(rep(1, m))), nrow = 1))
  Hr <- rbind(cbind("0", rep(as.character(as.bigq(B)), m), matrix(as.character(-as.bigq(diag(m))), nrow = m)),
              cbind("0", rep(as.character(as.bigq(B)), m), matrix(as.character( as.bigq(diag(m))), nrow = m)),
              ord_rows, eq_row)
  V <- scdd(Hr)$output; pts <- V[V[, 2] == "1", , drop = FALSE]
  if (nrow(pts) == 0L) return(NULL)
  pts[, -(1:2), drop = FALSE]
}

canon_key <- function(AFs, ATs, n) {
  g <- make_graph(edges = as.vector(rbind(AFs, ATs)), n = n, directed = TRUE)
  act <- which(degree(g, mode = "all") > 0); g <- induced_subgraph(g, act)
  paste(as.integer(as_adjacency_matrix(permute(g, canonical_permutation(g)$labeling), sparse = FALSE)), collapse = "")
}

enum_obstacles <- function(IDX) {
  A <- CE[[IDX]]; n <- nrow(A); arcs <- which(A == 1, arr.ind = TRUE)
  AF <- arcs[, 1]; AT <- arcs[, 2]; C <- length(AF)
  astar_f <- NA
  # column generation (free/signed y) -> orders G + float alpha
  G <- rbind(con(1:n, AF, AT, n), con(n:1, AF, AT, n))
  set.seed(7); G <- rbind(G, do.call(rbind, lapply(1:60, function(.) con(sample(n), AF, AT, n))))
  repeat {
    K <- nrow(G)
    ex <- lpcdd(makeH(d2q(cbind(G, matrix(-1, K, 1))), d2q(rep(0, K)),
                      d2q(matrix(c(rep(1, C), 0), nrow = 1)), d2q(1)),
                d2q(c(rep(0, C), 1)), minimize = TRUE)
    if (ex$solution.type != "Optimal") { G <- rbind(G, do.call(rbind, lapply(1:60, function(.) con(sample(n), AF, AT, n)))); next }
    astar <- as.bigq(ex$optimal.value); yv <- as.numeric(as.bigq(ex$primal.solution[1:C]))
    mo <- ewm_f(AF, AT, yv, n)
    if (mo$value <= as.numeric(astar) + 1e-9) break
    G <- rbind(G, con(mo$order, AF, AT, n))
  }
  astar_f <- as.numeric(astar); p <- as.integer(numerator(astar)); q <- as.integer(denominator(astar))

  # OUTER loop: [range-witness saturation -> flex/core] -> lrs VE -> vertex-witness saturation.
  # Range-witness saturation adds any order a per-arc range optimum violates AND enlarges the box if
  # a *valid* optimal dual reaches it -- so on exit the order-face is bounded (box non-binding) and
  # lrs sees the true (few-vertex) optimal-dual face rather than a box-dominated relaxation.
  supports <- NULL; sat <- 0L; nflex_final <- NA; box_bind <- FALSE
  repeat {
    repeat {                                    # --- range-witness saturation ---
      K <- nrow(G)
      Hq <- d2q(makeH(rbind(q * G, diag(C), -diag(C)), c(rep(p, K), rep(B, C), rep(B, C)),
                      matrix(rep(1, C), nrow = 1), 1))
      lo <- hi <- character(C); badc <- NULL; boxhit <- FALSE
      for (ee in 1:C) {
        og <- d2q(replace(numeric(C), ee, 1))
        rmn <- lpcdd(Hq, og, minimize = TRUE); rmx <- lpcdd(Hq, og, minimize = FALSE)
        if (rmn$solution.type != "Optimal" || rmx$solution.type != "Optimal")
          stop(sprintf("T%d range LP not optimal arc %d (%s/%s)", IDX, ee, rmn$solution.type, rmx$solution.type))
        lo[ee] <- rmn$optimal.value; hi[ee] <- rmx$optimal.value
        for (sol in list(rmx, rmn)) {
          yd <- as.numeric(as.bigq(sol$primal.solution)); mo <- ewm_f(AF, AT, yd, n)
          if (mo$value > astar_f + 1e-7) { badc <- con(mo$order, AF, AT, n); break }
          if (max(abs(yd)) > B - 1e-6) boxhit <- TRUE
        }
        if (!is.null(badc)) break
      }
      if (!is.null(badc)) { G <- unique(rbind(G, badc)); sat <- sat + 1L
        if (sat > 800L) stop(sprintf("T%d: range saturation did not converge", IDX)); next }
      if (boxhit) { B <- B * 10L; next }        # a valid dual reached the box -> enlarge and re-solve
      break                                     # ranges clean: all optima valid, box non-binding
    }
    loq <- as.bigq(lo); hiq <- as.bigq(hi)
    flex <- which(as.numeric(hiq - loq) > 1e-9); fix <- setdiff(1:C, flex); m <- length(flex)
    nflex_final <- m
    if (m == 0L) {                              # unique optimal dual -> single obstacle
      a <- which(as.numeric(abs(loq)) > TOL)
      supports <- list(list(supp = sort(a), neg = which(as.numeric(loq) < -TOL))); break
    }
    # exact VE of the (now order-bounded) signed flex polytope via lrs
    cfix <- loq[fix]; sflex <- as.bigq(1) - sum(cfix)
    Gf <- as.bigq(q) * as.bigq(G[, flex, drop = FALSE])
    rhs <- as.bigq(p) - (as.bigq(q) * as.bigq(G[, fix, drop = FALSE])) %*% cfix
    tsc <- Sys.time()
    vv <- flex_vertices_lrs(Gf, rhs, sflex, m, B)
    veng <- "lrs"; if (is.null(vv)) { vv <- flex_vertices_scdd(Gf, rhs, sflex, m, B); veng <- "scdd" }
    if (is.null(vv)) stop(sprintf("T%d: both lrs and scdd failed on flex polytope (m=%d)", IDX, m))
    if (Sys.getenv("VERB") == "1") cat(sprintf("    T%d sat-round %d: flex=%d, |G|=%d, %s verts=%d (%.1fs)\n",
        IDX, sat, m, nrow(G), veng, nrow(vv), as.numeric(Sys.time() - tsc, units = "secs")), file = stderr())
    bad <- NULL; vsupp <- list()
    for (k in seq_len(nrow(vv))) {
      yq <- as.bigq(rep(0, C)); yq[fix] <- cfix; yq[flex] <- as.bigq(vv[k, ])
      yd <- as.numeric(yq); if (max(abs(yd)) > B - 1e-6) box_bind <- TRUE
      mo <- ewm_f(AF, AT, yd, n)
      if (mo$value > astar_f + 1e-7) { bad <- c(bad, list(con(mo$order, AF, AT, n))); next }
      vsupp[[length(vsupp) + 1L]] <- list(supp = sort(which(as.numeric(abs(yq)) > TOL)),
                                          neg  = which(as.numeric(yq) < -TOL))
    }
    if (is.null(bad)) { supports <- vsupp; break }
    G <- unique(rbind(G, do.call(rbind, bad))); sat <- sat + 1L
    if (sat > 800L) stop(sprintf("T%d: vertex saturation did not converge", IDX))
  }
  # dedup supports within tournament + build keys (UNSIGNED support + SIGNED support = flip neg-weight arcs)
  obs <- list(); seen <- character(0)
  for (S in supports) {
    sp <- S$supp; fl <- sp %in% S$neg
    saf <- ifelse(fl, AT[sp], AF[sp]); sat <- ifelse(fl, AF[sp], AT[sp])   # flip negatively-weighted arcs
    k <- canon_key(AF[sp], AT[sp], n); sk <- canon_key(saf, sat, n)
    if (!(k %in% seen)) { seen <- c(seen, k)
      obs[[length(obs) + 1L]] <- list(idx = IDX, AF = AF[sp], AT = AT[sp], nS = length(sp),
                                      neg = S$neg, key = k, skey = sk, alpha = as.character(astar)) }
  }
  # per-tournament INCLUSION-MINIMAL flag: support does not literally contain another obstacle's support
  cds <- lapply(obs, function(o) sort(o$AF * 10L + o$AT))
  for (i in seq_along(obs)) { im <- TRUE
    for (j in seq_along(obs)) if (i != j && length(cds[[j]]) < length(cds[[i]]) && all(cds[[j]] %in% cds[[i]])) { im <- FALSE; break }
    obs[[i]]$incmin <- im }
  list(idx = IDX, n = n, alpha = as.character(astar), nflex = nflex_final, sat = sat,
       box_bind = box_bind, nobs = length(obs), obs = obs)
}

t0 <- Sys.time(); all_res <- list(); global_keys <- character(0)
if (file.exists(OUT)) {                                 # RESUME: keep banked tournaments, skip them
  all_res <- readRDS(OUT); done <- as.integer(names(all_res))
  global_keys <- unique(unlist(lapply(all_res, function(r) sapply(r$obs, function(z) z$key))))
  RANGE <- setdiff(RANGE, done)
  cat(sprintf("RESUME: %d already banked (%d distinct); %d tournaments remaining\n",
              length(done), length(global_keys), length(RANGE))); flush.console()
}
for (IDX in RANGE) {
  r <- enum_obstacles(IDX); all_res[[as.character(IDX)]] <- r
  global_keys <- unique(c(global_keys, sapply(r$obs, function(z) z$key)))
  cat(sprintf("[T%3d] alpha*=%-7s flex=%2d sat=%d obstacles=%2d  | global-distinct=%d  box_bind=%s (%.0fs)\n",
              r$idx, r$alpha, r$nflex, r$sat, r$nobs, length(global_keys), r$box_bind, as.numeric(Sys.time() - t0, units = "secs")))
  flush.console(); saveRDS(all_res, OUT)
}
cat(sprintf("\nDONE %d tournaments in %.0fs; GLOBAL DISTINCT obstacles = %d -> %s\n",
            length(RANGE), as.numeric(Sys.time() - t0, units = "secs"), length(global_keys), OUT))

# ---- build the distinct catalogue: 72 extreme-dual classes, each flagged inclusion_minimal ----
# (extreme-dual = all vertices of the optimal-dual face; inclusion_minimal = B.7's subset, TRUE if
#  the class is an inclusion-minimal support in at least one tournament).  Cover is 25 over either.
CATOUT <- Sys.getenv("NM1_CATALOG", sub("\\.rds$", "_catalog.rds", OUT))
{
  # inclusion_minimal (B.7): TRUE if the class is an inclusion-minimal support in >=1 tournament
  im_keys <- character(0)
  for (z in all_res) { ob <- z$obs; cds <- lapply(ob, function(o) sort(o$AF * 10L + o$AT))
    for (i in seq_along(ob)) { im <- TRUE
      for (j in seq_along(ob)) if (i != j && length(cds[[j]]) < length(cds[[i]]) && all(cds[[j]] %in% cds[[i]])) { im <- FALSE; break }
      if (im) im_keys <- c(im_keys, ob[[i]]$key) } }
  im_keys <- unique(im_keys)
  obs_all <- do.call(c, lapply(all_res, function(z) z$obs)); keys <- sapply(obs_all, function(o) o$key)
  dist <- obs_all[!duplicated(keys)]
  distinct <- lapply(dist, function(o) {
    vs <- sort(unique(c(o$AF, o$AT))); rl <- integer(max(vs)); rl[vs] <- seq_along(vs); k <- length(vs)
    D <- matrix(0L, k, k); D[cbind(rl[o$AF], rl[o$AT])] <- 1L
    list(src_idx = o$idx, alpha = o$alpha, D = D, key = o$key, nv = k, ne = length(o$AF),
         inclusion_minimal = (o$key %in% im_keys)) })
  saveRDS(list(distinct = distinct, n_tournaments = length(all_res), n_total_obstacles = length(obs_all),
               n_inclusion_minimal = sum(sapply(distinct, function(x) x$inclusion_minimal))), CATOUT)
  cat(sprintf("catalogue: %d extreme-dual classes (%d inclusion-minimal) -> %s\n",
              length(distinct), sum(sapply(distinct, function(x) x$inclusion_minimal)), CATOUT))
}
