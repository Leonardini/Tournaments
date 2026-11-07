# Appendices — shared engines and appendix-specific tools (`appendices/`)

**What it does.** This folder collects the cross-cutting engines used elsewhere in the
package and the tools tied to the paper's appendices. `hk_oracle.c` is the shared weighted
maximum-acyclic-subgraph (MAS) oracle (the exact weighted MAS of the appendix on integer and linear
programming formulations), meant to be compiled into the C tools that need it. The R scripts cover
the formulations of that appendix: the predictability LP that returns α\* together with the edge-dual
"obstacle" it certifies (`k_realizability_lp.R`) and the minimum set cover of obstacle classes
(`minimum_set_cover.R`). The obstacle appendix is served by the obstacle catalogue at n = 9
(`obstacle_catalogue/`, with its own README), the triple-local constraint search that scales the
3-inducibility census (`margin1_scan.c`), and the forced-arc reversal scanner (`reversal_check.c`).

**Files.**
- `hk_oracle.c` — weighted Held–Karp MAS oracle for n ≤ 16; **include, not standalone** (defines `hk_best(...)`, has no `main`).
- `k_realizability_lp.R` — predictability / realizability LP (α\* via primal, obstacle via edge duals) plus the n = 8/9 obstacle-family analysis; an Rcplex function library, not a self-running script.
- `minimum_set_cover.R` — minimum set cover of obstacle classes by ILP; function library with a small built-in demo, also `source`d by `k_realizability_lp.R`.
- `margin1_scan.c` — decides 3-inducibility, and 3-inducibility with unit margin, as a labelling of the vertex triples (about 20 µs per tournament); the engine of the census table.
- `reversal_check.c` — forced-arc reversal dichotomy scanner over `gentourng` bit-strings.

**Dependencies.** C (`cc -O3`) for `hk_oracle.c`, `margin1_scan.c` and `reversal_check.c`; R for the `.R`
tools (`Rcplex`, plus `pracma`, `combinat`, `Matrix`, `slam`, `igraph` depending on the script).
Versions and installation are in the [top-level README](../README.md#environment).
The CPLEX-only scripts here are **`k_realizability_lp.R` and
`minimum_set_cover.R`** (both via `Rcplex`); these have **no free-solver twin** — running them
requires IBM CPLEX 22.1. `hk_oracle.c`, `margin1_scan.c` and `reversal_check.c` need only a C compiler.

`k_realizability_lp.R` also `source`s sibling files: `Utilities.R`, `HittingSet.R`, and
`minimum_set_cover.R`. Of these, only `minimum_set_cover.R` is present in this folder — see the
run notes below.

**How to run.**

```sh
# --- hk_oracle.c is an INCLUDE, never run alone ---
# A C tool that needs the MAS oracle does:  #include "hk_oracle.c"
# then calls  double v = hk_best(W, n, order);   and is built normally, e.g.:
#   cc -O3 -o some_tool some_tool.c        # some_tool.c #includes hk_oracle.c

# --- minimum set cover (built-in 5-set / 5-element demo) ---
Rscript minimum_set_cover.R                        # needs Rcplex

# --- predictability LP and obstacle duals (function library) ---
# It is sourced, then a function is called. Single-tournament use:
Rscript -e 'source("k_realizability_lp.R"); \
            T <- matrix(c(0,1,1,0, 0,0,1,0, 0,0,0,1, 1,1,0,0), 4, 4, byrow=TRUE); \
            str(solve_realizability_lp(T))'
# Full n=8/9 obstacle-family analysis (writes Non3RealisabilitySummary.RData):
#   Rscript -e 'source("k_realizability_lp.R"); main()'
# main() also needs Utilities.R + HittingSet.R and the Counterexamples/ and
# Tournaments/ .RData inputs, none of which live in this folder.

# --- the triple-local census engine ---
cc -O3 -o margin1_scan margin1_scan.c
./margin1_scan 9 < ../data/mckay/tournaments9.txt     # tallies on stderr (see the header of margin1_scan.c)

# --- forced-arc reversal dichotomy ---
cc -O3 -o reversal_check reversal_check.c
./reversal_check 10 < hits.txt                      # n=10 gentourng bit-strings on stdin
./reversal_check 10 stats < hits.txt                # add the gained-3-cycles histogram
```

**What to expect.**

- **`hk_oracle.c`** — no runtime of its own; it is compiled into its includers. `hk_best`
  runs a Held–Karp DP (O(2ⁿ·n)), i.e. instant for n ≤ 16. In this package no committed C file
  actually `#include`s it; it is provided as the shared MAS engine for tools that need one.

- **`minimum_set_cover.R`** — *approximate:* under a second (tiny demo). Prints an
  `====`-ruled `Minimum Set Cover Problem` banner, `Sets: 5` / `Elements: 5`, `Solving ILP...`,
  then a `SOLUTION` block: `Status: <s> (Optimal)`, `Objective: 2 sets selected`, one
  `<name> (covers <k> elements)` line per chosen set, and `Total elements covered: 5/5`.

- **`k_realizability_lp.R`** — on `source` it prints `[1] "Pre-generating permutations"` then
  `1`…`8` (pre-builds `PERMS1`…`PERMS8`). `solve_realizability_lp(T)` prints
  `Building realizability LP for tournament of order <n>`, `Using <p> permutations`,
  `Processing row <i>` per row, and `LP has <v> variables, <c> constraints (<e> edge + 1 sum)`,
  returning `list(status, objective = α*, primal, edge_dual_map)`. *Approximate:* the 4-vertex
  demo is instant; `main()` is the expensive path — it enumerates factorial(n) permutation
  columns and solves an LP per tournament across the n = 8/9 censuses, so runtime scales with
  census size and factorial(n) and can run long. `main()` writes `ObstructionC8.pdf` and
  `Counterexamples/Non3RealisabilitySummary.RData`.

- **`reversal_check.c`** — to stdout, one line only for the interesting tournaments:
  `CEX u->v <bitstring>` (a forced-unanimous arc whose reversal stays 3-realizable) or
  `NOFORCED <bitstring>` (no forced-unanimous arc); the conjecture-holding case is tallied
  silently. To stderr: a progress line every 10000 tournaments
  `... <tot> (ok <ok> / noforced <nf> / cex <cex>)`, then the summary
  `n=<n>: total <tot>, conjecture-OK <ok>, NOFORCED <nf>, CEX <cex>` and
  `forced-arc count histogram (1..6,7+): …`; with `stats`, also
  `gained-3-cycles histogram over forced arcs (g: kills / survives):` and per-g
  `  g=<g>: <kills> / <survives>`. *Approximate:* runtime scales with the number of input
  tournaments times m per-tournament 4-label CSP solves (plus one reversal solve per forced arc);
  no committed timing here.
