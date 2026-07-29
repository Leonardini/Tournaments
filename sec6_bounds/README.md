# §6 — Improved bounds on N(k)  (`sec6_bounds/`)

**What it does.** Brackets N(5), the number of voters needed to realize every
tournament as a majority. The lower bound comes from an **exhaustive n = 11
census**: every one of the D₁₁ = 903,753,248 eleven-vertex tournaments is shown
5-inducible, so N(5) ≥ 12 — a **solver-free C** pipeline run at HPC scale. Its
core is a **triple-local CSP** engine that decides 3- and 5-inducibility as a
per-vertex-triple arc-labelling in microseconds. An independent **ILP
cross-check** re-settles the n ≤ 10 layer (N(5) > 10) with CPLEX. The upper
bound comes from **exact counting** against Schrijver's regular-tournament lower
bound and a completion-uniqueness argument (Proposition 6.1), giving N(5) ≤ 39
(regular) and, via a near-regular refinement, ≤ 38.

## Subfolders & files

### `n11_census/` — the N(5) ≥ 12 census (solver-free C, HPC)
The headline result: every 11-vertex tournament is 5-inducible. **Fully
documented in its own docs — see [`n11_census/README.md`](n11_census/README.md)
(pipeline, validation, running) and [`n11_census/RESULTS.md`](n11_census/RESULTS.md)
(the aggregate tally).** Drivers: `n11_worker.sh` (one gentourng res/mod slice,
streamed through the three CSP tools), `n11_aggregate.sh` (per-slice consistency
+ completeness check against D₁₁), `n11_census.slurm` (SLURM array fallback).

### `triple_local_csp/` — the CSP engines (C)
- `margin1_scan.c` — triple-local CSP deciding margin-1 3-realizability (3
  labels) and full 3-realizability (4 labels), per gentourng bitstring; ~20 µs/
  tournament (Appendix G.3). Emits `R`/`N` lines for the downstream stages.
- `cert_m1k5.c` — margin-1 five-voter CSP over the 10 dissent pairs; SAT ⇒
  5-inducible with every arc backed exactly 3:2, and emits the full arc-labelling
  as a witness.
- `verify_m1k5.c` — independent verifier: rebuilds the five voters from each
  witness, checks every backward set is acyclic and re-counts every arc at
  exactly 3:2; aborts on any failure, passes UNSAT lines through.

### `ilp10/` — the n ≤ 10 ILP cross-check (R, CPLEX)
- `solve_ilp10.R` — per-worker 5-realizability sweep of the n = 10 catalogue: a
  3-ILP pre-pass (3-realizable ⇒ 5-realizable) then a 5-ILP only on the
  3-infeasibles; status 103 would be a proven 5-infeasible (N(5) ≤ 10).
  Checkpointed/resumable. Uses `cplexAPI` via the shared `ilp_realizability.R`.
- `ilp10_aggregate.R` — combines the worker slices into the n = 10 verdict,
  naming any missing workers before claiming a definitive bound.

### `counting_bounds/` — the N(5) ≤ 39 / 38 upper bounds (Python)
- `extended_table1_bounds.py` — exact multiset counting + regular
  completion-uniqueness (Schrijver LB) → the extended Table 1 of nᵀ(k) bounds;
  the k = 5 entry is the regular bound N(5) ≤ 39. Reproduces the published [2]
  Lemma-2 thresholds as a built-in self-check.
- `nearreg_table_bounds.py` — near-regular (even-n) refinement via the proved
  bijection #near-regular(n) = RT(n+1); tightens k = 5 to N(5) ≤ 38. Includes a
  brute-force check of the bijection at small even n.

## Dependencies

Versions and installation are in the [top-level README](../README.md#environment).

- **`n11_census/`** — C compiler (`cc -O3`) + nauty 2.8.6 `gentourng`; bash. No
  solver: the census is **CPLEX-free**.
- **`triple_local_csp/`** — C compiler (`cc -O3`); nauty `gentourng` to feed
  bitstrings for whole-catalogue runs. No external libraries.
- **`ilp10/`** — R with the shared `ilp_realizability.R` engine and **`cplexAPI`
  (IBM CPLEX 22.1)**. The **only CPLEX scripts in this section** are
  `ilp10/solve_ilp10.R` and `ilp10/ilp10_aggregate.R`; the headline n = 11
  census needs no solver.
- **`counting_bounds/`** — Python 3, standard library only (`math`).

## How to run

**`counting_bounds/`** (no arguments):
```sh
python3 counting_bounds/extended_table1_bounds.py
python3 counting_bounds/nearreg_table_bounds.py
```

**`triple_local_csp/`** (build, then feed gentourng bitstrings; n = 9 shown as a
quick whole-catalogue demo):
```sh
cc -O3 -o margin1_scan triple_local_csp/margin1_scan.c
cc -O3 -o cert_m1k5    triple_local_csp/cert_m1k5.c
cc -O3 -o verify_m1k5  triple_local_csp/verify_m1k5.c

# stage 2 alone: 3-inducibility scan over all n = 9 tournaments
gentourng -q 9 | ./margin1_scan 9 emitn > /dev/null

# full margin-1 five-voter pipeline (the census wiring, one process)
gentourng -q 9 | ./margin1_scan 9 emitn | grep '^N ' | cut -d' ' -f2 \
  | ./cert_m1k5 9 | ./verify_m1k5 9 > /dev/null
```

**`ilp10/`** (CPLEX; run from a dir holding `ilp_realizability.R`; HPC-scale — a
200-way worker split over the n = 10 catalogue `<n10-data>`, a chunk dir or a
single `.RData`):
```sh
# one worker slice (worker 0 of 200); optional trailing args are t3 t5 ckpt_secs
Rscript ilp10/solve_ilp10.R 0 200 <n10-data> ilp10/results
# ... run all 200 workers (an HPC array) ...
Rscript ilp10/ilp10_aggregate.R ilp10/results 200
```

**`n11_census/`** (HPC job — see [`n11_census/README.md`](n11_census/README.md)
for building the tools into `bin/` and staging the kit):
```sh
# Local: 256 gentourng res/mod slices on 8 cores, then aggregate
seq 0 255 | xargs -P 8 -I{} bash n11_census/n11_worker.sh {} 256 results bin \
    ~/Downloads/DownloadedSoftware/nauty2_8_6/gentourng
bash n11_census/n11_aggregate.sh results 256

# HPC (SLURM array, 64 tasks), then aggregate
sbatch --array=0-63 n11_census/n11_census.slurm
bash n11_census/n11_aggregate.sh $WORK/n11_census 64
```

## What to expect

- **`counting_bounds/`** — ~a few seconds each (big-integer arithmetic + tiny
  brute-force loops; approximate). `extended_table1_bounds.py` prints the table
  `k paper exact reg_wit_n nT_reg best_nT margin_bits short_at_n-2` (one row per
  odd k = 3..21) and runs clean only if its asserts pass — they reproduce the
  published [2] Lemma-2 thresholds and check witness monotonicity, so an
  `AssertionError` would flag any mismatch. `nearreg_table_bounds.py` prints
  `== bijection check  #near-regular(n) == RT(n+1) ==` with per-n `OK`/`MISMATCH`
  lines, then the parity witness table and the k = 5 bit-margin. Section upshot:
  N(5) ≤ 39 (regular), ≤ 38 (near-regular).

- **`triple_local_csp/`** — ~20–34 µs/tournament for `margin1_scan`, ~276 µs/
  instance for `cert_m1k5` (per the census docs; approximate), so the n = 9 demo
  above (191,536 tournaments) is seconds. Final stderr lines (real wording):
  `margin1_scan` prints `n=9: total ..., margin1-SAT ..., REALIZABLE-NOT-MARGIN1
  ..., non-realizable ...`; `cert_m1k5` prints `total ...: margin1-k5-SAT ...,
  UNSAT ...`; `verify_m1k5` prints `verified ... margin-1-k5 witnesses (all exact
  3:2); ... UNSAT passed through` — or aborts with `VERIFY FAIL (<reason>):
  <line>` on any bad witness. (At n = 9 the known answer is total 191,536 /
  margin1-SAT 173,608 / not-margin1 254 / non-realizable 17,674, all 5-SAT and
  verified.)

- **`ilp10/`** — an HPC-scale batch (200 workers over the 9.7M-tournament n = 10
  catalogue); wall-clock depends on the cluster. The 3-ILP settles the vast
  majority in milliseconds; the 5-ILP (default `t5 = 300 s` cap) runs only on the
  3-infeasible minority; both are approximate. Each worker writes
  `ilp10/results/ilp10_wNNN.RData` and prints `[ilp10 wNNN] DONE  3feas=..
  5feas(via5)=..  5INFEAS=..  inconclusive=..`. The aggregator prints
  `ILP 5-realizability sweep of ... tournaments on n=10 ...` with the per-verdict
  breakdown and, when complete and clean, `All 200 workers reported. Every n=10
  tournament is 5-realizable => N(5) > 10, settled definitively.` (a `status 103`
  count > 0 would instead announce a proven N(5) ≤ 10 counterexample).

- **`n11_census/`** — HPC/large: ~4.5–5.5 h wall on 8 local cores, or the SLURM
  array (64 tasks, 3 h walltime each); wall-clock depends on the cluster / node
  count (all approximate). `n11_aggregate.sh` prints the tally, the
  `COMPLETENESS CHECK PASSED: total == D_11 == 903,753,248` line, and
  `=> every 11-vertex tournament is 5-inducible: N(5) >= 12  [PROVEN, no ILP
  needed]`. See [`n11_census/RESULTS.md`](n11_census/RESULTS.md) for the full
  aggregate.
