# Independent reproduction of arXiv 2607.26690 — Paley(43) is not the majority of five voters

[![Open in molab](https://marimo.io/molab-shield.svg)](https://molab.marimo.io/github/Leonardini/Tournaments/blob/main/paley43_five_voters.py)

**Claim tested.** The paper's headline computational result (§7): the Paley tournament on 43
vertices is *not* 5-realizable — it is the Kemeny median of no five linear orders — hence
**N(5) ≤ 43**. Equivalently, α\* > 3/5 does **not** imply 5-inducibility, refuting Conjecture A.

**What was done.** A 5-realization would need two rankings at level ≤ 1 (within 1 arc of the
maximum acyclic subgraph) whose *double-back sets* are disjoint. The screen that rules this out
was run **exhaustively over the complete level-0 shell** — all 17,744,853 maximum-acyclic orders
of Paley(43) — in two independent modes, with the package's positive-detection control and an
independent re-derivation of the automorphism lemma the screen's reduction rests on. Three
further censuses were reproduced at **full published scale** alongside it.

**Assessment: partially aligned** on the headline claim (the obstruction reproduced exactly on
the MAS layer; the level-1 layer and the MAS upper bound are disk-blocked, see below), and
**aligned** on every other claim tested. Across all nodes: **46 claim checks aligned, 2
divergent — both traced to their cause, neither affecting a paper claim — 1 partial.**

| headline numbers | paper | observed |
|---|---|---|
| **TRUE_DISJOINT** over the level-0 shell | **0** | **0** (twice: automorphism-reduced *and* reduction-free) |
| candidate pairs exactly checked | 333,809 | 333,809 |
| level-0 orders screened | 17,744,853 | 17,744,853 |
| minimum double-back overlap | 68 | 71 automorphism-reduced → **68** in the paper's mode |
| MAS(Paley(19)/(23)/(31)) | 107 / 161 / 285 | **107 / 161 / 285** |
| FAS = HS₃, every tournament n ≤ 10 | 0 violations | **0** over **9,932,002** tournaments |
| n = 9 census tally | 191,536 / 173,608 / 254 / 17,674 | **exact on every line** |
| cA3: α\* on the A(3) threshold, not 3-inducible | 2/3 exactly, not 3-inducible | **2/3 exactly**, not 3-inducible (**3/3** independent engines) |

**Downscaling and substitutions.** One deliberate downscale: the screen ran on the **level-0**
shell (19,651 orbits / 17.7 M orders) rather than the full **level ≤ 1** shell (1,841,303 orbits
/ 1.66 B orders). Rebuilding the level-≤ 1 layer tables needs **~48 GB of scratch** (the engine's
own Burnside ceiling is 48.28 GB) and this machine had **43 GB free on a 96 %-full boot volume**,
so it was not attempted. Consequently MAS(Paley43) **≥ 543** was re-derived here independently
while **≤ 543** still rests on the paper's certification, and what is established is that no
5-realization can have *both* top voters at level 0. The n = 11 census ran on **7** parallel
workers rather than the documented 8, because each slice is a 4-process pipeline and this laptop
is held to 10 cores — same computation, longer wall clock. Nothing else was substituted: McKay's
n = 9 and n = 10 catalogues and nauty `gentourng` were used as the package specifies, and CPLEX
22.1 was present so no CPLEX check was skipped.

**Compute.** The author's Mac (14 cores, 24 GB RAM; Apple clang 16, R 4.5.3, Python 3.12.13,
OR-Tools 9.15.6755, CPLEX 22.1.2.0, GLPK), every run launched through `orx exp run --backend
local` and capped at 8 threads. Everything except the n = 11 census cost **about five minutes of
wall clock total** (307 s across seven runs), at 0.23 GB peak resident memory.

**Read the details:** [`reports/paley43-five-voters/report.md`](reports/paley43-five-voters/report.md)
— the full write-up: the mechanism, the code path, five figures, and the per-claim assessment
table. The [marimo notebook](paley43_five_voters.py) is a tutorial version that opens with the
evidence and re-derives the cheap parts live (structure constants, the co-backing lemma); it
needs no expensive computation. Run it locally with `marimo edit paley43_five_voters.py` (or
`marimo run paley43_five_voters.py` for the read-only app), or open it in Molab with the badge
above.

## Experiment log

Every node runs the **same** command over different code — that is the contract, so results stay
comparable. Reproduce any node by checking out its branch and running the command verbatim.

| branch / experiment | purpose or change | exact run command | outcome | compute |
|---|---|---|---|---|
| [`main`](https://github.com/Leonardini/Tournaments/tree/main) | publication surface: this README, the report, the notebook | Not run as an experiment (publication surface) | — | — |
| [baseline](https://github.com/Leonardini/Tournaments/tree/orx/baseline-package-wide-fast-verification-check-al) | run the package's own quick verifier `check_all.sh` unchanged | `bash repro/run.sh` | **aligned** — 12/12 PASS, 0 FAIL (CPLEX present, so the usually-skipped check ran too) | local, 1 core, 68 s |
| [S7-A](https://github.com/Leonardini/Tournaments/tree/orx/s7-a-mas-engine-certification-paley-43-premises) | add the full Appendix A.4 MAS gauntlet (q = 19/23/31) and `repro/verify_d0.c`, an independent re-derivation of the level-0 premises | `bash repro/run.sh` | **aligned** — MAS 107/161/285 certified; 19,651 reps all at fwd = 543, stabiliser-free, distinct orbits ⇒ 17,744,853 | local, 8 threads, 15 s |
| [S7-B](https://github.com/Leonardini/Tournaments/tree/orx/s7-b-exhaustive-level-0-razor-screen-the-co-back) | run `razor_screen` exhaustively over the complete level-0 shell | `bash repro/run.sh` | **aligned on the claim** — TRUE_DISJOINT = 0, \|R\| = 538, 333,809 pairs; `min_overlap` 71 vs 68 (diagnosed in S7-C) | local, 8 threads, 9 s |
| [S7-C](https://github.com/Leonardini/Tournaments/tree/orx/s7-c-screen-soundness-controls-the-min-overlap-d) | add `repro/verify_ginv.c`; run the screen's controls via its existing knobs `DBTEST=1` and `POOLVSPOOL=1` | `bash repro/run.sh` | **aligned** — coverage control 333,809 = 333,809; reduction-free run gives TRUE_DISJOINT = 0 and `min_overlap` = **68**; 0 invariance violations in 1,598,310 checks | local, 8 threads, 25 s |
| [S4](https://github.com/Leonardini/Tournaments/tree/orx/s4-theorem-4-1-fas-hs3-for-every-tournament-on-n) | sweep `hs3fas` over complete catalogues for every n from 3 to 10 | `bash repro/run.sh` | **aligned** — 9,932,002 tournaments, 0 with HS₃ < FAS, 0 unresolved | local, 1 core, 116 s |
| [S6-D](https://github.com/Leonardini/Tournaments/tree/orx/s6-d-triple-local-csp-engine-at-n-9-full-census) | validate the census engine over the complete n = 9 catalogue before spending hours on n = 11 | `bash repro/run.sh` | **aligned** — tally exact on every line; all 17,674 witnesses independently re-verified | local, 1 core, 10 s |
| [S6-D1](https://github.com/Leonardini/Tournaments/tree/orx/s6-d1-n-11-census-every-11-vertex-tournament-is) | the N(5) ≥ 12 census: all D₁₁ = 903,753,248 tournaments, 256 slices | `bash repro/run.sh` | **in flight** — projected ~8.5 h wall / ~60 core-hours; resumed from 46 banked slices after a watchdog false positive | local, 7 workers |
| [S7-D](https://github.com/Leonardini/Tournaments/tree/orx/s7-d-full-level-1-shell-the-complete-paley-43-pr) | the complete proof: rebuild the q = 43 layer tables and run the screen over the full level-≤ 1 shell | `bash repro/run.sh` | **queued** — pre-flight refuses below 60 GB free; volume has 40 GB. Launches unchanged once there is headroom | local, 8 threads, ~48 GB scratch |
| [S5-E](https://github.com/Leonardini/Tournaments/tree/orx/s5-e-ca3-battery-the-k-3-threshold-is-necessary) | the cA3 battery: exact α\*, all three non-3-inducibility engines, 5-inducibility, vertex-criticality, minimal certificate | `bash repro/run.sh` | **aligned** — α\* = 2/3 exactly, not 3-inducible 3/3 engines, 5-inducible, vertex-critical, 6-order certificate. Surfaced a README error: cA3 is **not** doubly regular | local, 1–2 cores, 50 s |

The harness is three files: [`repro/env.sh`](repro/env.sh) is the fixed environment contract
(identical on every branch — paths, thread cap, and a memory watchdog that charges swap growth to the run only when the run's own RSS could plausibly cause it);
[`repro/verify_d0.c`](repro/verify_d0.c) and [`repro/verify_ginv.c`](repro/verify_ginv.c) are the
two independent verifiers written for this reproduction, sharing no code with the package's
engines. Each branch carries its own `repro/run.sh`, which is the only thing that varies.
Figures are regenerated by [`repro/figures/make_figures.py`](repro/figures/make_figures.py).

**Two divergences, both explained.** (1) `min_overlap` 71 vs 68: it is a diagnostic, not the
claim, and it is a property of *which candidate set is scored*. The automorphism reduction
preserves the *existence* of a zero-overlap pair, but razor-disjointness is not itself
automorphism-invariant, so the two modes score different sets; re-running in the paper's mode
returns 68 exactly. (2) `sec5_a3_boundary/README.md` states cA3 is doubly regular; the script
correctly prints otherwise — cA3's triangles-per-arc distribution is {2: 22, 3: 11, 4: 22}, since
the doubly regular circulant on 11 vertices is Paley(11), a different connection set. No claim
depends on it.

---

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
