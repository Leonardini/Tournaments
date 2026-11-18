# Appendix C — the 12-vertex counterexample W12 (`appC_every_order/`)

**What it does.** Appendix C shows that Conjecture 2 of Milosz–Hamel–Pierrot (FAS = HS₃ on 3-inducible
tournaments) fails at every order n ≥ 11. The orders n ≥ 13 and the rotational tournaments are settled by proof;
the one computed ingredient is the 12-vertex tournament W12 (T\* with the arc 7 → 1 reversed, plus a vertex 12
beaten only by 7), whose values this folder computes.

**Level 0 — check the result (free tools, about 1 s).**
```sh
python3 verify_appendix_c.py          # needs ortools; prints ALL APPENDIX C CHECKS PASS
```
It rebuilds T\* and W12 from the paper's 3-voter profiles and computes FAS with an exact subset DP and HS₃
(the fewest arcs meeting every directed 3-cycle) with CP-SAT: W12 is strong, has 60 directed 3-cycles, the
paper's order leaves 17 arcs backward, FAS = 17 and HS₃ = 16.

**Level 1 — reproduce as found (needs Gurobi).**
- `appendix_conj2_certs.py` — finds a 3-voter profile for W12 by ILP and solves FAS and HS₃ to proven
  optimality (build the exact DP first: `cc -O3 -o mas_dp mas_dp.c`). Output: `appendix_conj2_certs_output.txt`.
- `mas_dp.c` — exact FAS by Held–Karp subset DP. `hs3.py` — the Gurobi FAS and HS₃ models the script imports.
