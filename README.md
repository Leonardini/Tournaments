> **Independent reproduction (2026-07-30).** Every computational claim in this package was
> re-run on a single laptop, including the §7 keystone end to end: the q=43 layer tables rebuilt
> from scratch, `MAS(Paley43) = 543` certified both ways, the level-≤1 shell enumerated and
> census-verified at 1,841,303 orbits, and `TRUE_DISJOINT = 0` over all 4,376,325,129 pairs —
> every published count exact. See **[REPRODUCTION.md](REPRODUCTION.md)** for the claim-by-claim
> table and experiment log, **[reports/paley43-five-voters/report.md](reports/paley43-five-voters/report.md)**
> for the illustrated write-up, and **[paley43_five_voters.py](paley43_five_voters.py)** for a
> tutorial notebook.
>
> *Note for anyone rebuilding §7 on a machine with under ~32 GB of RAM:* run
> `CHUNKMB=2 ./reproduce_paley43.sh`. The default chunk size puts ~6.4 GB into buffers and peaks
> near 26 GB at layer 20; `CHUNKMB=2` completed the same layers at ~9 GB.

# Tournaments determined by three and five voters — reproducibility package

Code for the paper *Tournaments determined by three and five voters*
(L. Chindelevitch and A. Harutyunyan). Every computational claim in the paper has a verifier here,
organized by section, with a claim → tool manifest further down.

Two ways in:

- **Check the results fast** — from the repo root, `./check_all.sh` (~1–2 min) runs a quick
  "check the result" step for every section and reports PASS / FAIL. Free tools only: no HPC, no
  downloads, no CPLEX.
- **Reproduce the keystone end-to-end** — the headline result (Paley(43) is not the majority of five
  voters, §7 ⇒ **N(5) ≤ 43**) rebuilds from one script:
  `cd sec7_paley43 && ./reproduce_paley43.sh` (details under *Quick start* below).

The package is **source-only** (≈ 2.5 MB). Large data — McKay's tournament catalogues, the Paley(43)
DP layer tables — is not checked in; the scripts regenerate it or download it (see *Data policy*).
Most claims are cross-checked by two independent engines (e.g. CPLEX *and* OR-Tools CP-SAT, or an ILP
*and* a solver-free check), and every reported optimum is re-verified in exact rational arithmetic.

## Requirements

You need a **C compiler**, **R**, and **Python 3**. No script needs all of it — each says what it uses.

- **C** (`cc -O3`) — the DP / CSP engines and screens.
  - `sec5_a3_boundary/alpha_fast.c` also needs [GLPK](https://www.gnu.org/software/glpk/).
  - the n = 11 census also needs [nauty 2.8.6](https://pallini.di.uniroma1.it/) `gentourng`.
  - `appendices/hk_oracle.c` is an `#include`d oracle, not a standalone program.
- **R** — `igraph` (graphs, every figure), `lpSolve` (LP seed; FAS/HS₃ checks), and `rcdd` + `gmp`
  (exact rational LP and big-rational arithmetic — the exact α\* verification). The solver-free
  obstacle checker `sec5_a3_boundary/verify_obstacle_certs.R` needs **only `gmp`**. `combinat`,
  `slam`, `Matrix`, `pracma`, and `tidyverse` cover incidental helpers.
- **Python 3** — OR-Tools CP-SAT (`ortools`), `pulp`, `networkx`.
- **Data** — McKay's digraph catalogues: <https://users.cecs.anu.edu.au/~bdm/data/digraphs.html>.

**CPLEX is optional** (see below); `cplexAPI` / `Rcplex` and `docplex` / `cplex` are used only by the
handful of CPLEX scripts.

### CPLEX (optional)

**No headline result needs it.** Paley(43) (§7), the N(5) ≥ 12 census (§6), FAS = HS₃ (§4), and cA3's
non-3-inducibility (§5) all run with just a C compiler and/or free solvers (OR-Tools CP-SAT, PuLP-CBC,
`lpSolve`, GLPK). Only these eight scripts use IBM CPLEX 22.1 — and the reproducibility ones each have
a free twin:

| CPLEX script | free twin |
|---|---|
| `sec5_a3_boundary/reg11_realize3.py` | `independent_realize3_cpsat.py` |
| `sec5_a3_boundary/n10_realize3.py` | `cpsat_realize3_n10.py` |
| `sec5_a3_boundary/cert_primal_1068.py` | `cert_orbits_1068.py` |
| `sec6_bounds/ilp10/solve_ilp10.R`, `ilp10_aggregate.R` | `sec6_bounds/ilp10/verify_5inducible.py` |
| `appendices/{gen_duals.R, k_realizability_lp.R, minimum_set_cover.R}` | — (appendix computations only) |

To run the CPLEX scripts, install **IBM ILOG CPLEX Optimization Studio 22.1** (free for academics via
the [IBM Academic Initiative](https://www.ibm.com/academic)), then add the bindings:

- **Python:** `python <cplex-studio>/python/setup.py install` — the full library; the
  `pip install cplex` community edition caps models at 1000 variables.
- **R:** `install.packages("Rcplex", configure.args="--with-cplex-dir=<cplex-studio>/cplex")`;
  `cplexAPI` (CRAN archive) builds the same way.

## Quick start — the Paley(43) result (§7)

```sh
cd sec7_paley43 && ./reproduce_paley43.sh
```

This builds `dp43.c`, `canon_reps.c`, `razor_screen.c`, then runs, in order:

1. **self-tests** — the MAS gauntlet on q = 7, 11 (brute force) and q = 19, 23, 31 (against known values);
2. the **δ ≤ 2 layer tables**;
3. the **level-≤ 1 shell** with a census identity check (orbit count must equal 1,841,303);
4. the **co-backing screen** ⇒ **N(5) ≤ 43**.

Needs ≤ 8 threads, ~5 GB RAM, and ~50 GB scratch disk. `d0_reps.txt` (the δ = 0 orbit representatives)
is the one committed input; every other table is regenerated.

## Manifest — claim → verifier

Theorem 2.1 (§2, *every minimum FAS is a minimal 3-cycle hitting set*) is proved analytically (paper
Appendix A) and needs no computation. Everything below does.

### §3 — Refuting Conjecture 1 of Milosz–Hamel–Pierrot (`sec3_mhp/`)

| claim | tool |
|---|---|
| Counterexamples 3.1 (m = 7, 9) and 3.2 (m = 5, n = 6): FAS > HS₃, with the minimum-weight FAS found by brute force and the margins verified | `make_family_and_mhp_figs.R` — self-checking; **stops on any mismatch** before plotting |

### §4 — Conjecture 2: FAS = HS₃ on 3-inducible tournaments (`sec4_fas_hs3/`)

| claim | tool |
|---|---|
| Theorem 4.1: FAS = HS₃ for **every** tournament on n ≤ 10 (exhaustive) | `hs3fas.c` — Held–Karp MAS + exact minimum 3-cycle hitting set over a McKay catalogue |
| Counterexample 4.2: regular T\* on 11 vertices with FAS = 17 > 16 = HS₃ | `make_tstar_figs.R` — self-checks FAS = 17 and HS₃ = 16 (lpSolve) |
| The six 3-inducible self-converse violators (Figure 4) | `make_conj2_cex_figs.R` — re-checks self-converse and HS₃ < FAS |

### §5 — The A(3) threshold fails on the boundary (`sec5_a3_boundary/`)

cA3 is the code's **ce1068**: the Z₁₁ circulant with connection set {1, 2, 3, 4, 6}.

| claim | tool |
|---|---|
| cA3 structure and exact α\* = 2/3 (rational, `rcdd`/GMP) | `verify_ce1068.R`, `analyze_ce1068.R`, `inmask_alpha.R` |
| cA3 not 3-inducible — three independent methods | `reg11_realize3.py` (CPLEX), `independent_realize3_cpsat.py` (CP-SAT), `realize3_partition.c` (solver-free) |
| 6-order 2/3-certificate; minimality; orbit-minimality | `cert_primal_1068.py`, `cert_orbits_1068.py`, `enum_profiles.c`, `make_cA3_fig.R` |
| cA3 is 5-inducible; vertex-criticality | `realize_and_delete_ce1068.py` |
| regular n = 11 census (1,223) isolating cA3 | `reg11_alphastar.R`, `reg11_realize3.py` |
| n = 10 census (9,733,056 → 1,013 counterexamples) | `n10_prefilter.R`, `extract_gidx_inm.py`, `alpha_fast.c`, `n10_realize3.py`, `cpsat_realize3_n10.py`, `batch_verify_alpha_n10.R`, `characterize_n10_ce.R` |
| cA6 (needs **9** voters); the 6-vs-9-voter dichotomy | `cert9.c` |
| forced-arc reversal counterexamples at n = 10 (Figure 8) | `make_reversal_cex_figs.R` |

### §6 — Improved bounds on N(k) (`sec6_bounds/`)

| claim | tool |
|---|---|
| N(5) ≥ 12: every tournament on n ≤ 11 is 5-inducible (n = 11 census over D₁₁ = 903,753,248) | `n11_census/` pipeline (`n11_worker.sh`, `n11_aggregate.sh`) driving `triple_local_csp/{margin1_scan.c, cert_m1k5.c}`; independent re-verifier `triple_local_csp/verify_m1k5.c` |
| the n ≤ 10 ILP layer (CPLEX; free twin `verify_5inducible.py`) | `ilp10/solve_ilp10.R`, `ilp10/ilp10_aggregate.R`, `ilp10/make_chunks10.R` |
| triple-local CSP — 3-inducibility as a vertex-triple labelling (~20 µs/tournament; Appendix G.3) | `triple_local_csp/margin1_scan.c` |
| Proposition 6.1 completion-uniqueness ⇒ N(5) ≤ 39 (regular), ≤ 38 (near-regular) | `counting_bounds/extended_table1_bounds.py`, `counting_bounds/nearreg_table_bounds.py` |

### §7 — Paley(43) is not the majority of five voters (`sec7_paley43/`)

Run it via *Quick start* above. The pieces:

- `dp43.c` — certifies MAS(Paley(43)) = 543 (the Appendix E engine);
- `canon_reps.c` — enumerates the level-≤ 1 shell;
- `razor_screen.c` — runs the co-backing screen;
- `realize5_cpsat.py --gauntlet` — validates the CP-SAT 5-inducibility encoder used for auxiliary checks.

Proof write-up: [`PALEY43_NONREALIZABLE.md`](sec7_paley43/PALEY43_NONREALIZABLE.md).

### Appendices — shared engines and appendix-specific tools (`appendices/`)

| appendix | tool |
|---|---|
| B.6 — predictability LP α\* (column generation, exact MAS oracle as separator); obstacle duals (Appendix G.1) | `k_realizability_lp.R` |
| B.4 — minimum set cover of obstacle classes | `minimum_set_cover.R` |
| B.7 — enumerate all minimal obstacle supports | `gen_duals.R` |
| E — MAS engine: weighted Held–Karp oracle (n ≤ 16) | `hk_oracle.c` |
| G.2 — forced-arc reversal dichotomy | `reversal_check.c` |
| G — obstacle figures (G₈, G₉ role-labelled) | `make_AB_obstacle_figures.R` |

The infinite obstacle family (a forthcoming companion paper) is **not** included here.

## Data policy

No large data is committed — scripts regenerate it (`reproduce_paley43.sh` rebuilds every DP table) or
read McKay catalogues you download from the link above. Two small inputs are the exceptions, kept in
the repo: `sec7_paley43/d0_reps.txt` (2.2 MB, the δ = 0 orbit-representative seed) and
`data/regulartournaments11.RData` (40 KB, the 1,223 regular 11-vertex tournaments the cA3 scripts read).

## Layout

```
sec3_mhp/          §3  MHP Conjecture 1 counterexamples
sec4_fas_hs3/      §4  Conjecture 2 (FAS = HS₃): n ≤ 10 census + T*
sec5_a3_boundary/  §5  A(3) threshold on the boundary: cA3, censuses, cA6
sec6_bounds/       §6  bounds on N(k): n = 11 census, ILP, counting
sec7_paley43/      §7  Paley(43), end-to-end from one script
appendices/        shared engines + appendix-specific tools (B, E, G)
common/  data/     shared α* oracle; the few committed data inputs
```
