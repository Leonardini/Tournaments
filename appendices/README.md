# Appendices — shared engines and appendix-specific tools (`appendices/`)

**What it does.** This folder collects the cross-cutting engine used elsewhere in the
package and the tools tied to the paper's appendices. `hk_oracle.c` is the shared weighted
maximum-acyclic-subgraph (MAS) oracle (Appendix E), meant to be compiled into the C tools that
need it. The R scripts cover the Appendix B computations — the realizability / predictability LP
that returns α\* together with the edge-dual "obstacle" it certifies (`k_realizability_lp.R`,
B.6 / obstacle duals), the minimum set cover of obstacle classes (`minimum_set_cover.R`, B.4),
and a diverse family of triangle-packing dual certificates on Paley(43) for the budget-DP
complement bound (`gen_duals.R`, listed under B.7). Appendix G is served by the forced-arc
reversal-dichotomy scanner (`reversal_check.c`, G.2) and the obstacle-collection figure
generator (`make_AB_obstacle_figures.R`, G).

**Files.**
- `hk_oracle.c` — weighted Held–Karp MAS oracle for n ≤ 16 (Appendix E); **include, not standalone** (defines `hk_best(...)`, has no `main`).
- `k_realizability_lp.R` — predictability / realizability LP (α\* via primal, obstacle via edge duals) plus the n = 8/9 obstacle-family analysis (Appendix B.6, obstacle duals G.1); an Rcplex function library, not a self-running script.
- `minimum_set_cover.R` — minimum set cover of obstacle classes by ILP (Appendix B.4); function library with a small built-in demo, also `source`d by `k_realizability_lp.R`.
- `gen_duals.R` — builds triangle-packing dual certificates on Paley(43) for the budget-DP complement bound (manifest label B.7).
- `reversal_check.c` — forced-arc reversal dichotomy scanner over `gentourng` bit-strings (Appendix G.2).
- `make_AB_obstacle_figures.R` — draws the obstacle collections A′ (26) and B′ (25) as PDFs (Appendix G).

**Dependencies.** C (`cc -O3`) for `hk_oracle.c` and `reversal_check.c`; R for the four `.R`
tools (`Rcplex`, plus `pracma`, `combinat`, `Matrix`, `slam`, `igraph` depending on the script).
Versions and installation are in the [top-level README](../README.md#environment).
The three CPLEX-only scripts here are **`gen_duals.R`, `k_realizability_lp.R`, and
`minimum_set_cover.R`** (all via `Rcplex`); these have **no free-solver twin** — running them
requires IBM CPLEX 22.1. `hk_oracle.c` and `reversal_check.c` need only a C compiler.

Two of the R scripts also `source` sibling files: `gen_duals.R` reads `cert_pool.R` (which
supplies `paley_adj`), and `k_realizability_lp.R` reads `Utilities.R`, `HittingSet.R`, and
`minimum_set_cover.R`. Of these, only `minimum_set_cover.R` is present in this folder — see the
run notes below.

**How to run.**

```sh
# --- Appendix E: hk_oracle.c is an INCLUDE, never run alone ---
# A C tool that needs the MAS oracle does:  #include "hk_oracle.c"
# then calls  double v = hk_best(W, n, order);   and is built normally, e.g.:
#   cc -O3 -o some_tool some_tool.c        # some_tool.c #includes hk_oracle.c

# --- Appendix B.4: minimum set cover (built-in 5-set / 5-element demo) ---
Rscript minimum_set_cover.R                        # needs Rcplex

# --- Appendix B.6 / obstacle duals: realizability LP (function library) ---
# It is sourced, then a function is called. Single-tournament use:
Rscript -e 'source("k_realizability_lp.R"); \
            T <- matrix(c(0,1,1,0, 0,0,1,0, 0,0,0,1, 1,1,0,0), 4, 4, byrow=TRUE); \
            str(solve_realizability_lp(T))'
# Full n=8/9 obstacle-family analysis (writes Non3RealisabilitySummary.RData):
#   Rscript -e 'source("k_realizability_lp.R"); main()'
# main() also needs Utilities.R + HittingSet.R and the Counterexamples/ and
# Tournaments/ .RData inputs, none of which live in this folder.

# --- Appendix B.7 label: triangle-packing duals on Paley(43) ---
# Usage: Rscript gen_duals.R <nsolves> <out.rds> [seed]
Rscript gen_duals.R 100 duals.rds 4343             # needs Rcplex + cert_pool.R
# NOTE: gen_duals.R does source("cert_pool.R") for paley_adj(); that file is NOT
# present in this folder, so the script cannot run here as shipped.

# --- Appendix G.2: forced-arc reversal dichotomy ---
cc -O3 -o reversal_check reversal_check.c
./reversal_check 10 < hits.txt                      # n=10 gentourng bit-strings on stdin
./reversal_check 10 stats < hits.txt                # add the gained-3-cycles histogram

# --- Appendix G: obstacle figures (run from the repo root per the script) ---
Rscript make_AB_obstacle_figures.R                  # reads Counterexamples/Non3RealisabilitySummary.RData
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

- **`gen_duals.R`** — first prints
  `[gen_duals] q=43 arcs=903 cyclic-triangles=3311 | panel 40 complements t=21, tau* mean <…>`;
  then every 10 solves
  `[  NN] novel: behavior <b>, multiset <m> | recovery mean(bestW/tau*) = <r> (min <r2>)`;
  and finally `[gen_duals] done: <N> packings -> <out.rds> | final recovery <r>`. It checkpoints
  `<out.rds>` every 50 solves (complete/loadable at any time). *Approximate:* runtime scales
  with `<nsolves>` — one continuous max-triangle-packing CPLEX LP (≈ 903 rows, 3311 columns) per
  solve; no exact per-solve timing is available here, and as shipped it stops immediately for
  lack of `cert_pool.R`.

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

- **`make_AB_obstacle_figures.R`** — asserts `length(Aprime) == 26` and `length(Bprime) == 25`,
  writes `Manuscript/figures/A_prime_01.pdf`…`A_prime_26.pdf`,
  `B_prime_01.pdf`…`B_prime_25.pdf`, and the grids `collectionA_prime.pdf`,
  `collectionB_prime.pdf`, then prints
  `Done: 26 A' + 25 B' figures + 2 grids in Manuscript/figures/`. *Approximate:* seconds to a
  minute (igraph `layout_with_kk` on ~50 small graphs). It requires
  `Counterexamples/Non3RealisabilitySummary.RData` (produced by `k_realizability_lp.R`'s
  `main()`) and an existing `Manuscript/figures/` directory — neither is in this folder.
