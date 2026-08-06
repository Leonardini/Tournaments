# =====================================================================================
# common/progress.R — the shared progress reporter for the longer-running R scripts.
#
# Base R only: nothing here computes anything, so it stays out of every certificate's
# trust path. It writes to *stderr*, so stdout — the result lines the checkers grep for —
# is byte-for-byte what it was. On a terminal you get one live line that rewrites itself;
# redirected to a file you get one line every 15 s; with PROGRESS=0 in the environment you
# get nothing.
#
# Usage (the caller stays runnable if this file is not next to it):
#   if (file.exists("../common/progress.R")) source("../common/progress.R") else
#     { progress <- function(...) invisible(); progress_done <- function() invisible() }
#   for (i in seq_len(n)) { ...; progress(i, n, "obstacles certified") }
#   progress_done()
# =====================================================================================

.progress_state <- new.env(parent = emptyenv())
.progress_state$t0   <- Sys.time()
.progress_state$last <- Sys.time()
.progress_state$on   <- !identical(Sys.getenv("PROGRESS"), "0")
.progress_state$tty  <- isatty(stderr())
.progress_state$live <- FALSE     # is there an unfinished live line on stderr?

progress <- function(i, n, what = "done") {
  st <- .progress_state
  if (!st$on) return(invisible())
  now <- Sys.time()
  gap <- if (st$tty) 0.5 else 15
  if (i < n && as.numeric(difftime(now, st$last, units = "secs")) < gap) return(invisible())
  st$last <- now
  el  <- as.numeric(difftime(now, st$t0, units = "secs"))
  eta <- if (i > 0 && i < n) sprintf(", ~%.0fs left", el * (n - i) / i) else ""
  line <- sprintf("  %s %d/%d (%.0f%%)  %.0fs%s", what, i, n, 100 * i / n, el, eta)
  if (st$tty) {
    cat("\r", line, sep = "", file = stderr()); st$live <- TRUE
  } else {
    cat(line, "\n", sep = "", file = stderr())
  }
  invisible()
}

progress_done <- function() {
  st <- .progress_state
  if (st$live) { cat("\n", file = stderr()); st$live <- FALSE }
  invisible()
}
