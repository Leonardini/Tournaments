#!/usr/bin/env Rscript
# =====================================================================================
# install_r_packages.R — install the R packages this reproducibility package needs.
#
#   Rscript install_r_packages.R          # the four core packages (all the quick checks)
#   Rscript install_r_packages.R --all    # core + the extras used by appendices/ and the
#                                         #   full-census pipelines
#
# Only missing packages are installed; anything already present is left alone. IBM CPLEX
# bindings (Rcplex, cplexAPI) are NOT installed here — they must be built against a local
# CPLEX Studio, and every script that uses them has a free twin (see README.md).
#
# System libraries first (the R packages below are thin wrappers over them):
#   macOS         brew install gmp mpfr glpk
#   Debian/Ubuntu apt-get install libgmp-dev libmpfr-dev libglpk-dev libxml2-dev
# =====================================================================================

core <- c(
  igraph  = "graphs, canonical forms, every figure",
  lpSolve = "the float LP seed in the column-generation alpha* oracle",
  rcdd    = "exact rational LP (the alpha* = 2/3 verification)",
  gmp     = "exact big-rational arithmetic (the solver-free certificate checks)"
)

extras <- c(
  combinat      = "appendices/: permutation helpers",
  Matrix        = "appendices/, ilp10/: sparse constraint matrices",
  slam          = "appendices/: sparse triplet matrices for the LP builders",
  pracma        = "appendices/k_realizability_lp.R",
  magrittr      = "appendices/: pipes",
  stringr       = "appendices/Utilities.R",
  gtools        = "appendices/HittingSet.R",
  matrixStats   = "appendices/HittingSet.R",
  tidyverse     = "appendices/: data wrangling in the exploratory tools",
  testthat      = "appendices/Utilities.R: its inline unit checks",
  microbenchmark = "appendices/HittingSet.R: timing helpers"
)

args <- commandArgs(trailingOnly = TRUE)
all  <- "--all" %in% args
want <- if (all) c(core, extras) else core

if (is.null(getOption("repos")) || getOption("repos")["CRAN"] %in% c(NA, "@CRAN@")) {
  options(repos = c(CRAN = "https://cloud.r-project.org"))
}

cat(sprintf("R %s.%s   library: %s\n", R.version$major, R.version$minor, .libPaths()[1]))
cat(sprintf("installing the %s set (%d packages)%s\n\n",
            if (all) "core + extras" else "core", length(want),
            if (all) "" else "  [use --all for the appendices/ extras]"))

have <- function(p) suppressWarnings(requireNamespace(p, quietly = TRUE))

missing <- names(want)[!sapply(names(want), have)]
for (p in names(want)) {
  if (p %in% missing) next
  cat(sprintf("  present  %-15s %s\n", p, as.character(packageVersion(p))))
}
if (length(missing) == 0L) {
  cat("\nnothing to do — every package in this set is already installed.\n")
  quit(save = "no", status = 0)
}

cat(sprintf("\nmissing (%d): %s\n\n", length(missing), paste(missing, collapse = ", ")))
install.packages(missing)

# Re-test, and fail loudly: a package that did not build is almost always a missing
# system library, and the message below is the one thing that tells you which.
still <- missing[!sapply(missing, have)]
cat("\n")
for (p in setdiff(missing, still)) cat(sprintf("  installed %-15s %s\n", p, as.character(packageVersion(p))))
if (length(still) > 0L) {
  cat(sprintf("\n  FAILED to install: %s\n", paste(still, collapse = ", ")))
  hints <- c(gmp    = "needs GMP        (brew install gmp        / apt-get install libgmp-dev)",
             rcdd   = "needs GMP        (brew install gmp        / apt-get install libgmp-dev)",
             igraph = "needs libxml2/glpk (brew install libxml2 glpk / apt-get install libxml2-dev libglpk-dev)")
  for (p in still) if (p %in% names(hints)) cat(sprintf("    %-15s %s\n", p, hints[p]))
  stop("some R packages could not be installed — see the messages above", call. = FALSE)
}
cat("\nall set. Next: ./check_env.sh\n")
