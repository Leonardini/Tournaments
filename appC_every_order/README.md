# Appendix C — Conjecture 2 at every order, and the rotational tournaments (`appC_every_order/`)

**What it does.** Backs the paper's Appendix C: Conjecture 2 of Milosz–Hamel–Pierrot
(FAS = HS₃ on 3-inducible tournaments) fails at every order n ≥ 11, the gap FAS − HS₃ takes every
positive value, and FAS = HS₃ = (n² − 1)/8 on every rotational tournament RT_n.

**Level 0 — check the result (free tools, about 10 s).**
```sh
python3 verify_appendix_c.py          # needs ortools; prints ALL APPENDIX C CHECKS PASS
python3 rt_totient_weights.py 120 3   # pure Python; prints "failures none"
```
`verify_appendix_c.py` rebuilds T\* from its 3-voter profile and checks, with an exact subset DP for FAS and
CP-SAT for HS₃: W12 (the paper's profile induces it; strong; 60 directed 3-cycles; the paper's order leaves
17 arcs backward; FAS = 17, HS₃ = 16); C3[T\*, TT₁, TT₁] (3-inducible by the block profile of the substitution
lemma; FAS = 18, HS₃ = 17); the substitution formulas on random substitutions; the explicit 3-voter profile of
RT_n for every odd n ≤ 201; and HS₃(RT_n) = (n² − 1)/8 directly for n ≤ 13 (CP-SAT needs minutes at n = 15,
which is why the proof exists).

`rt_totient_weights.py kmax [kmin]` checks the proof's certificate in exact rational arithmetic: with the
balanced copy B_m of each order weighted φ(g)/g, g = gcd(2m − 1, n), the load on every span is computed from
the exact span counts of the copies (not from the Fourier identity), and the resulting dual value exceeds
C(k, 2) − 1 for every k in range. `--profile` prints the flat load profile.

**Level 1 — reproduce as found (needs Gurobi).**
- `appendix_conj2_certs.py` — finds 3-voter profiles for W12 and C3[T\*, TT₁, TT₁] by ILP, solves FAS and HS₃
  to proven optimality, and cross-checks FAS with the exact DP (`cc -O3 -o mas_dp mas_dp.c` first). Output:
  `appendix_conj2_certs_output.txt`.
- `rt_hs3_certificate.py kmax` — the LP dual certificate over all balanced copies, as Gurobi finds it, then
  verified in exact arithmetic (k ≤ 150 in `rt_hs3_certificate_output.txt`). The φ(g)/g weights were read off these duals.
- `mas_dp.c` — exact FAS by Held–Karp subset DP; up to n = 34 (the n = 33 run for FAS(C3[T\*, T\*, T\*]) = 172
  needs an 8 GiB table). `hs3.py` — the Gurobi FAS/HS₃ models the two scripts import.
