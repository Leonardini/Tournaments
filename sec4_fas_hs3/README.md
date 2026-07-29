# §4 — Conjecture 2: FAS = HS₃ on 3-inducible tournaments  (`sec4_fas_hs3/`)

**What it does.** Backs the §4 claims about when the minimum feedback arc set (FAS)
equals the minimum 3-cycle hitting set (HS₃). `hs3fas.c` establishes **Theorem 4.1**
by exhaustively checking, over a McKay tournament catalogue, that FAS = HS₃ for every
tournament on n ≤ 10 vertices (FAS via an exact Held–Karp maximum-acyclic-subgraph DP,
HS₃ via exact branch-and-bound). The two R scripts regenerate the paper's figures for
the n = 11 counterexamples where the equality first fails: `make_tstar_figs.R` for the
regular tournament T\* (Counterexample 4.2 / Figure 3, FAS = 17 > 16 = HS₃), and
`make_conj2_cex_figs.R` for the six 3-inducible self-converse violators (Figure 4). Both
R scripts re-verify every numeric claim before drawing and halt on any mismatch.

**Files.**
- `hs3fas.c` — exhaustive FAS == HS₃ census over a McKay catalogue (Theorem 4.1).
- `make_tstar_figs.R` — rebuilds the T\* figures (Counterexample 4.2 / Figure 3), re-checking FAS = 17 and HS₃ = 16.
- `make_conj2_cex_figs.R` — rebuilds the six self-converse violator figures (Figure 4), re-checking self-converse and HS₃ < FAS.

**Dependencies.** C compiled with `cc -O3`; R with `igraph` and `lpSolve`. Versions and
installation are in the [top-level README](../README.md#environment). **None require
CPLEX** (the FAS = HS₃ census runs with only a C compiler and free solvers). `hs3fas.c`
reads an external **McKay tournament catalogue** — a plain-text file with one tournament
per line, each line a bit string of length C = n(n−1)/2 (the tournament's triangle of
arc directions); download it from the McKay digraph-catalogue link in the top-level
README's [Environment](../README.md#environment) section. The R scripts need no external
data (the tournaments are hard-coded from their Appendix C inducing profiles).

**How to run.**
```sh
# 1. hs3fas.c — exhaustive FAS == HS3 census (Theorem 4.1)
cc -O3 -o hs3fas hs3fas.c
# usage: ./hs3fas <catalogue.txt> <n>   (catalogue lines must have length n(n-1)/2)
./hs3fas tournaments10.txt 10        # e.g. the n = 10 McKay catalogue
#   repeat once per catalogue, e.g. ./hs3fas tournaments8.txt 8, ... up to n = 10

# 2. make_tstar_figs.R — Counterexample 4.2 / Figure 3 (takes no arguments)
Rscript make_tstar_figs.R           # writes PDFs to the current directory; run from this folder

# 3. make_conj2_cex_figs.R — the six self-converse violators / Figure 4 (takes no arguments)
Rscript make_conj2_cex_figs.R       # writes PDFs to the current directory; run from this folder
```

**What to expect.**

- **`hs3fas.c`** — runtime depends on the catalogue size (number of tournaments, which
  grows sharply with n): small catalogues (n ≤ 8) finish in seconds; the full n = 10
  catalogue (≈ 9.7 million tournaments) is the longest, on the order of minutes
  (approximate — not measured here). Prints a final summary line, e.g.
  `n=10: 9733056 tournaments; 0 with HS3<FAS; 0 HARD (unresolved) => minFAS == for ALL minHS3`.
  For Theorem 4.1 the mismatch and HARD counts are both 0, giving the `== for ALL`
  verdict. Any refutation prints up to 20 lines like
  `MISMATCH idx <k>: FAS=<f> HS3=<h>  bits=<line>`; any branch-and-bound blow-up prints
  up to 20 `HARD idx <k> (B&B node limit, FAS=<f>): bits=<line>` lines (the node limit is
  20,000,000). Writes no files (all output to stdout).

- **`make_tstar_figs.R`** — a few seconds. Prints
  `FAS check: witness order leaves 17 arcs backward`, `cyclic triangles: <count>`, and
  `HS check: minimum 3-cycle hitting set has 16 arcs`, then `Tstar_HS.pdf written` and
  `Tstar_FAS.pdf written`. Writes `Tstar_HS.pdf` and `Tstar_FAS.pdf` to the working
  directory. Guarded by `stopifnot`: it aborts if T\* is not regular (out-degree 5), if
  the witness order does not leave exactly 17 backward arcs, or if the exact minimum
  3-cycle hitting set is not 16.

- **`make_conj2_cex_figs.R`** — a few seconds (six exact Held–Karp DPs over 2¹¹
  subsets). For each of A–F prints, e.g.,
  `Counterexample A: self-converse OK, HS3 = <h> < <f> = FAS` followed by
  `CounterexampleA.pdf written`. Writes `CounterexampleA.pdf` … `CounterexampleF.pdf` to
  the working directory. Guarded by `stopifnot`: it aborts if any tournament is not
  self-converse (`vf2` isomorphism to its converse) or fails HS₃ < FAS.
