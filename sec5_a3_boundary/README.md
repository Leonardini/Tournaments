# §5 — The A(3) threshold fails on the boundary (cA3)  (`sec5_a3_boundary/`)

**What it does.** Conjecture A(k) predicts that a tournament is *k*-inducible (the majority of some *k* voters) exactly when its predictability α\* reaches the threshold (k+1)/(2k). This folder shows the k = 3 threshold α\* = 2/3 is **not** sufficient: it exhibits and certifies **cA3** — the code's **`ce1068`**, the Z₁₁ circulant tournament with connection set {1, 2, 3, 4, 6} (`allGraphs[[1068]]`) — which has exactly α\* = 2/3 yet is **not** 3-inducible (it needs 5 voters). It then isolates cA3 inside the regular n = 11 census and the full n = 10 census, and records the companion object cA6 (which needs 9 voters), plus the two boundary figures.

**Files.**

*cA3 structure & exact α\* = 2/3*
- `verify_ce1068.R` — independent end-to-end recompute of `allGraphs[[1068]]`: exact rational α\* = 2/3 with re-checked certificate; emits its inmask.
- `analyze_ce1068.R` — automorphism group, circulant connection set {1,2,3,4,6}, double-regularity, and the α\*=2/3 dual (obstacle) certificate.
- `inmask_alpha.R` — exact rational α\* for every tournament in an arbitrary inmasks file.

*cA3 is not 3-inducible — three independent methods*
- `reg11_realize3.py` — **CPLEX** k = 3 majority ILP (also drives the n = 11 census).
- `independent_realize3_cpsat.py` — OR-Tools **CP-SAT** (position-var encoding), hardcoded cA3, tests k = 3 and k = 5.
- `realize3_partition.c` — solver-free: enumerate all 11! backward masks, search for a 3-order partition of the 55 arcs.

*6-order certificate; minimality; orbit-minimality*
- `cert_primal_1068.py` — **CPLEX** min-cardinality primal 2/3-certificate (fewest certifying orders).
- `cert_orbits_1068.py` — free (PuLP/CBC): how few C₁₁-orbits a 2/3-certificate can use (k = 1 impossible, k = 2 search).
- `enum_profiles.c` — enumerate all 11! orders, emit the exact set of C₁₁ orbit-profiles (makes the 2-orbit search rigorous).

*cA3 is 5-inducible; vertex-criticality*
- `realize_and_delete_ce1068.py` — CP-SAT: explicit 5-voter realization + 3-realizability of the (unique) n = 10 deletion.

*Regular n = 11 census (1,223 tournaments)*
- `reg11_alphastar.R` — exact rational α\* over all 1,223 regular n = 11 tournaments (distribution vs the 2/3 threshold).
- `reg11_realize3.py` — the k = 3 ILP applied across the census (CPLEX; see above).

*n = 10 census (9,733,056 tournaments → 1,013 counterexamples)*
- `alpha_fast.c` — fast **float** α\* filter (GLPK master LP + C MAS DP) classifying α\* = 2/3 vs < 2/3.
- `batch_verify_alpha_n10.R` — exact rational confirmation that each survivor has α\* = 2/3.
- `n10_realize3.py` — **CPLEX** k = 3 ILP over a chunk, deciding 3-realizability.
- `cpsat_realize3_n10.py` — OR-Tools **CP-SAT** twin of the n = 10 3-realizability check.
- `characterize_n10_ce.R` — structural profile (|Aut|, regularity, self-converse, degree sequences) of the n = 10 counterexamples.

*cA6 — the 6-vs-9-voter dichotomy*
- `cert9.c` — decide existence of a 9-voter 2/3-certificate (CSP; cA6 needs 9 voters).

*Figures*
- `make_cA3_fig.R` — Figure 5 (`cA3.pdf`), the circulant drawing; self-checks the six-order 2/3-certificate.
- `make_reversal_cex_figs.R` — Figure 8, the four n = 10 forced-arc reversal counterexamples.

**Dependencies.**
- **C** (`cc -O3`); GLPK for `alpha_fast.c` (links `-lglpk`). `cert9.c`, `enum_profiles.c`, `realize3_partition.c`, `alpha_fast.c` are standalone (no shared include).
- **Python 3** with OR-Tools CP-SAT (`ortools`) and PuLP (`pulp`); IBM CPLEX (`cplex`) for the three CPLEX scripts only.
- **R** with `igraph`, `lpSolve`, `rcdd`, `gmp`. The α\* scripts (`verify_ce1068.R`, `analyze_ce1068.R`, `inmask_alpha.R`, `reg11_alphastar.R`, `batch_verify_alpha_n10.R`) `source` the shared column-generation MAS oracle `alpha_star.R` and load the regular-tournament catalogue `regulartournaments11.RData`; several also write outputs under a `Paley23Decide/` directory. Ensure those inputs are reachable from your run directory.
- **CPLEX scripts here and their free-solver twins** (so a CPLEX-less user has a full path):
  `reg11_realize3.py` → `independent_realize3_cpsat.py`;
  `n10_realize3.py` → `cpsat_realize3_n10.py`;
  `cert_primal_1068.py` → `cert_orbits_1068.py`.

Versions and installation are in the [top-level README](../README.md#environment).

**How to run.** Free solvers are shown as the default; the CPLEX alternative is noted inline.

```sh
# --- cA3 structure & exact alpha* = 2/3 ---
Rscript verify_ce1068.R                 # writes .../ce1068_inmask.txt
Rscript analyze_ce1068.R                # connection set {1,2,3,4,6}, dual cert
Rscript inmask_alpha.R Paley23Decide/ce1068_inmask.txt

# --- cA3 is NOT 3-inducible (three independent methods) ---
python3 independent_realize3_cpsat.py            # CP-SAT (free) — default
cc -O3 -o realize3_partition realize3_partition.c
./realize3_partition                             # solver-free confirmation
# CPLEX alternative (single-tournament inmask from verify_ce1068.R):
# python3 reg11_realize3.py Paley23Decide/ce1068_inmask.txt ce1068_realize3.csv

# --- 6-order certificate; minimality / orbit-minimality ---
python3 cert_orbits_1068.py                      # PuLP/CBC (free) — default
cc -O3 -o enum_profiles enum_profiles.c && ./enum_profiles
# CPLEX alternative (min-cardinality primal certificate):
# python3 cert_primal_1068.py

# --- cA3 is 5-inducible; vertex-criticality ---
python3 realize_and_delete_ce1068.py

# --- regular n = 11 census (1,223) ---
Rscript reg11_alphastar.R                        # all 1,223; optional: NMAX OUT.rds
# 3-realizability across the census (CPLEX): python3 reg11_realize3.py reg11_inmasks.txt reg11_realize3.txt

# --- n = 10 census (9,733,056 tournaments) ---
cc -O2 -o alpha_fast alpha_fast.c -I/opt/homebrew/include -L/opt/homebrew/lib -lglpk
./alpha_fast chunk00.inm                         # fast float filter: "idx MAS alpha"
Rscript batch_verify_alpha_n10.R n10_ce.inm n10_ce.gidx n10_ce_astar.txt   # exact 2/3 confirm
python3 cpsat_realize3_n10.py n10_ce.inm n10_ce.gidx        # CP-SAT (free) 3-realizability
# CPLEX alternative: python3 n10_realize3.py chunk00.tin chunk00.csv
Rscript characterize_n10_ce.R n10_ce.inm

# --- cA6: 9-voter certificate ---
cc -O3 -o cert9 cert9.c
./cert9 <n> < cA6_bits.txt                        # bitstrings = upper-triangle arc bits, one per line

# --- figures ---
Rscript make_cA3_fig.R                            # -> cA3.pdf (Figure 5)
Rscript make_reversal_cex_figs.R                  # -> ReversalCEX_{A,B,C,D}.pdf (Figure 8)
```

**What to expect.** Timings are approximate (single core; none measured here).

- **cA3 structure (`verify_ce1068.R`, `analyze_ce1068.R`, `inmask_alpha.R`)** — a few seconds each (one n = 11 tournament; 2¹¹ DP oracle + exact `rcdd` LP). `verify_ce1068.R` prints `alpha* = 2/3 (0.6666666667) [rcdd status Optimal]`, `certificate re-check: ... TRUE`, `alpha* == 2/3 exactly ? TRUE`, and writes `ce1068_inmask.txt`. `analyze_ce1068.R` prints `|Aut|` (C₁₁), `has an 11-cycle automorphism (=> circulant): TRUE`, `circulant connection set S ... {1, 2, 3, 4, 6}`, `doubly-regular (all==3): TRUE`, and the dual-certificate support, saving `ce1068_analysis.rds`. `inmask_alpha.R` prints one `... alpha* = 2/3 (0.66667) ... [alpha* = 2/3]` line per input tournament.

- **Not-3-inducible, three methods** — `independent_realize3_cpsat.py`: seconds; prints `n=11, arcs=55 ... out-regular deg-5 tournament: OK`, then `k=3 (maj>=2): INFEASIBLE (proven)` and `k=5 (maj>=3): FEASIBLE`. `realize3_partition.c`: ~1–3 min (enumerates 11! = 39,916,800 orders, then partition search); stderr `E=55` + back-count histogram, stdout `NO PARTITION EXISTS => ce1068 is NOT 3-realizable (third, solver-free confirmation).` CPLEX `reg11_realize3.py` on the single inmask returns `NOTREAL=1`.

- **Certificate / minimality** — `cert_orbits_1068.py`: seconds; prints `(1) column generation: ... alpha* = 0.666667`, `arc-orbits under C_11: 5 classes, sizes [11, 11, 11, 11, 11]`, `k=1 feasible in pool? False`, and the k = 2 orbit-pair result (or `No 2-orbit certificate within the pool. => ... minimum is 3 orbits`). `enum_profiles.c`: tens of seconds to a couple of minutes (11! perms × 55 arcs); stderr `E=55 classes=5` + `perms=39916800 distinct-profiles=...`, stdout the profile lines. CPLEX `cert_primal_1068.py`: seconds; prints `(3) CPLEX min-cardinality = 6 orders`, `(4) exact min-edge-agreement = 2/3 ... certifies >= 2/3: True; tight edges: 55/55`, then the 6-order minimal certificate.

- **5-inducibility / vertex-criticality (`realize_and_delete_ce1068.py`)** — seconds; prints `(E) full n=11: 5-realizable = True  => McG = 5 (not 3, but 5)`, `verification: arcs with < 3 voters agreeing = 0`, and `(D) delete 1 vertex (n=10 ...): 3-realizable = True` → `VERTEX-CRITICAL for non-3-realizability`.

- **Regular n = 11 census (`reg11_alphastar.R`)** — order tens of minutes for all 1,223 (per-tournament exact α\*; the script prints its own `(…s/tourn)` rate and checkpoints an `.rds`); scales linearly with `NMAX`. Ends with the α\* distribution split into `< 2/3`, `== 2/3` (the boundary, containing cA3), `> 2/3`.

- **n = 10 census (heaviest)** — the full census is **9,733,056** tournaments. Runtime scales with the number of tournaments processed and with n (each engine does a 2ⁿ DP or a small ILP), and is meant to be **chunked/parallelised**:
  - `alpha_fast.c` is the cheap pre-filter (per-tournament sub-ms once MAS-rejected; MAS < ⌈2C/3⌉ ⇒ `alpha = -1`). Sweeping all 9.7M on one core is order **hours**; it emits `idx MAS alpha` per line.
  - `n10_realize3.py` (CPLEX) / `cpsat_realize3_n10.py` (CP-SAT) then decide 3-realizability on the survivors — a small ILP/CP each, so runtime tracks the survivor count (≈1,013 counterexamples); running one CPLEX ILP over all 9.7M single-threaded would be **CPU-days**. CPLEX prints `DONE ...: REAL=... NOTREAL=... INC=...`; CP-SAT prints per-line `k=3 CP-SAT -> INFEASIBLE` and `SUMMARY: N INFEASIBLE (not 3-real), M feasible/unknown (expect all INFEASIBLE)`.
  - `batch_verify_alpha_n10.R` (exact) and `characterize_n10_ce.R` run over the ~1,013 counterexamples: minutes to tens of minutes, scaling with line count. `batch_verify` prints `DONE ...: alpha*=2/3 exactly: N ; other: M (of T)`; `characterize` prints the |Aut| table, `regular ...: 0`, self-converse count, and the canonical first example.

- **cA6 (`cert9.c`)** — per-tournament CSP; runtime depends on the input list size (fast per line, with stderr progress every 1,000). Prints `Y <line>`/`N <line>` and a final `total N: cert9-SAT Y, UNSAT U` — a `Y` confirms a 9-voter 2/3-certificate exists.

- **Figures** — seconds each. `make_cA3_fig.R` prints `cA3 checks passed: tournament, regular (out-deg 5), all 55 arcs tight at 4/6 = 2/3` and `cA3.pdf written`. `make_reversal_cex_figs.R` prints one `ReversalCEX_X written; forced arc u -> v` line per case, writing four PDFs.

---

# Non-margin-1 obstacle census (exact-coverage predictability α⁼)  — `enumerate_nm1_supports.R` et al.

**What it does.** For the **254** tournaments on `n = 9` that are 3-inducible **but not with margin 1**
(Appendix G.2), it produces the *complete* obstacle census, certifies every obstacle's
exact-coverage predictability `α⁼ = p/q < 2/3` **solver-free** (`gmp` only), and computes the minimum
set cover. Here the inducibility LP's optimal duals are **signed** (the "exact-coverage variant" of
B.7), so an obstacle is the support of an *extreme optimal signed dual*.

**Results.** 254 tournaments → **72 distinct extreme-dual obstacle classes** (of which **54** are
inclusion-minimal supports in the B.7 sense — carried as the `inclusion_minimal` flag on each class);
all 72 exactly certified `α⁼ = p/q < 2/3`, taking the **11** values
`21/32 23/35 25/38 27/41 29/44 31/47 35/53 37/56 39/59 41/62 45/68`; **minimum set cover = 25**
(CPLEX-optimal, and optimal over both the 72- and 54-class catalogues).

**Antichain caveat.** B.7's "the solutions form an antichain = inclusion-minimal supports" is correct
**per tournament** but does **not** hold for the pooled catalogue: the 54 inclusion-minimal classes
have 14 cross-tournament isomorphic containments (the 72 extreme-dual classes have 51), because
inclusion-minimality is local and `α⁼` is anti-monotone along containment. See
`Manuscript/ObstacleAntichain_RevisionNote.md`. `nm1_containment.R` reports all of this.

**Files.**
- `enumerate_nm1_supports.R` — the enumerator (the one solver step besides minting). Exact vertex
  enumeration of each tournament's signed optimal-dual face: exact per-arc ranges (`rcdd`) →
  flex/core split → range-witness saturation (bounds the face so the box is non-binding) → exact VE
  of the low-dim flex polytope by **lrs** (reverse search; `scdd` fallback) → vertex-witness
  saturation. Writes the per-tournament raw output and the deduplicated catalogue
  `../data/n9_nm1_obstacle_catalog.rds` (each class: `alpha`, `D`, `key`, `inclusion_minimal`).
  Resumable (banks each tournament); `NM1_DATA`, `LRS_BIN`, `NM1_CATALOG` are env-overridable.
- `mint_nm1_obstacle_certs.R` — mints the exact primal + **signed**-dual certificate for each of the
  72 classes (`rcdd` + `gmp`; float column-gen seed, exact confirmation) →
  `n9_nm1_obstacle_certs.rds`. This is the only solver step; its output is re-checked **solver-free**
  by `verify_nm1_obstacle_certs.R`, so `rcdd`/CPLEX are not in the trust path.
- `verify_nm1_obstacle_certs.R` — **solver-free** static checker (`gmp` only): primal `x ≥ 0`,
  `Σx = 1`, **exact-equality** coverage `p/q` (⇒ `α⁼ ≥ p/q`); signed `y`, `Σy = 1`, exact signed
  Held–Karp weighted-MAS `≤ p/q` (⇒ `α⁼ ≤ p/q`); asserts `p/q < 2/3`. No LP/cdd/CPLEX.
- `nm1_set_cover.R` — containment matrix (igraph vf2 non-induced monomorphism) + minimum set-cover
  ILP (CPLEX) → `../data/n9_nm1_obstacle_cover.rds` (25 classes).
- `nm1_containment.R` — the containment poset / antichain analysis (extreme-dual vs inclusion-minimal;
  anti-monotonicity; cover = antichain of minimal obstacles).
- Data: `../data/n9_margin1only_tournaments.rds` (the 254 tournaments),
  `../data/n9_nm1_obstacle_catalog.rds` (catalogue), `../data/n9_nm1_obstacle_cover.rds` (cover),
  `n9_nm1_obstacle_certs.rds` (certs).

**Dependencies.** R with `igraph`, `rcdd`, `gmp`, `Rcplex`; the **lrs** binary (lrslib) for the
enumerator (point `LRS_BIN` at it). Only `gmp` is needed to re-check the certificates.

**How to run.**
```sh
Rscript verify_nm1_obstacle_certs.R n9_nm1_obstacle_certs.rds   # gmp-only: 72/72, all α⁼ = p/q < 2/3
Rscript nm1_containment.R                                       # 72 extreme-dual / 54 inclusion-minimal; cover antichain
Rscript nm1_set_cover.R                                         # rebuild containment + 25-class cover (CPLEX)
# regenerate from scratch (needs lrs + rcdd):
LRS_BIN=/path/to/lrs Rscript enumerate_nm1_supports.R "1:254" nm1_face_out.rds   # -> catalogue
Rscript mint_nm1_obstacle_certs.R                              # -> n9_nm1_obstacle_certs.rds
```
