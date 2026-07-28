#!/usr/bin/env python3
# reg11_realize3.py — decide 3-realizability of every regular tournament on 11 vertices, SINGLE-THREAD.
# Reads reg11_inmasks.txt (one tournament per line: inm[v] = bitmask of in-neighbours u of v, arc u->v).
# For each: k=3 majority ILP (3 linear orders; each arc forward in >= 2 of them). FEASIBLE => 3-realizable;
# proven infeasible => NOT 3-realizable. Cross-checks Conjecture A (3-realizable iff alpha* >= 2/3):
# theorem says 3-realizable => alpha* >= 2/3, so any alpha*<2/3 MUST be NOT-3-realizable; a counterexample
# is an alpha* >= 2/3 tournament that comes back NOT-3-realizable.
import sys, cplex, time
INM = sys.argv[1] if len(sys.argv) > 1 else "Paley23Decide/reg11_inmasks.txt"
OUT = sys.argv[2] if len(sys.argv) > 2 else "Paley23Decide/reg11_realize3.txt"
OFFSET = int(sys.argv[3]) if len(sys.argv) > 3 else 0   # add to printed idx (parallel chunks)
n, k, maj = 11, 3, 2
pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]

def solve(inm):
    A = [[1 if (inm[v] >> u) & 1 else 0 for v in range(n)] for u in range(n)]  # A[u][v]=1 => arc u->v
    cpx = cplex.Cplex(); cpx.set_results_stream(None); cpx.set_log_stream(None); cpx.set_warning_stream(None)
    yidx = {}; names = []; t = 0
    for p in range(k):
        for (u, v) in pairs:
            yidx[(p, u, v)] = t; names.append(f"y_{p}_{u}_{v}"); t += 1
    cpx.variables.add(types=[cpx.variables.type.binary] * t, names=names)
    rows = []; sen = []; rhs = []
    for p in range(k):                                  # transitivity per voter, per triple
        for u in range(n):
            for v in range(u + 1, n):
                for w in range(v + 1, n):
                    ind = [yidx[(p, u, v)], yidx[(p, v, w)], yidx[(p, u, w)]]
                    rows.append(cplex.SparsePair(ind=ind, val=[1, 1, -1])); sen.append("L"); rhs.append(1.0)
                    rows.append(cplex.SparsePair(ind=ind, val=[1, 1, -1])); sen.append("G"); rhs.append(0.0)
    for (u, v) in pairs:                                 # majority agreement with the arc
        ind = [yidx[(p, u, v)] for p in range(k)]
        if A[u][v] == 1: rows.append(cplex.SparsePair(ind=ind, val=[1] * k)); sen.append("G"); rhs.append(float(maj))
        else:            rows.append(cplex.SparsePair(ind=ind, val=[1] * k)); sen.append("L"); rhs.append(float(k - maj))
    cpx.linear_constraints.add(lin_expr=rows, senses=sen, rhs=rhs)
    cpx.parameters.threads.set(1)                        # SINGLE THREAD (laptop core budget)
    cpx.parameters.timelimit.set(120)
    cpx.solve()
    sts = cpx.solution.get_status_string()
    feas = cpx.solution.is_primal_feasible()
    verdict = "REAL" if feas else ("NOTREAL" if "infeasible" in sts.lower() else "INCONCLUSIVE")
    return verdict, sts

lines = [l.split() for l in open(INM) if l.strip()]
t0 = time.time()
with open(OUT, "w") as f:
    f.write("idx,verdict,status\n")
    nreal = nnot = ninc = 0
    for idx, toks in enumerate(lines):
        inm = [int(x) for x in toks]
        v, s = solve(inm)
        nreal += v == "REAL"; nnot += v == "NOTREAL"; ninc += v == "INCONCLUSIVE"
        f.write(f"{idx+OFFSET},{v},{s}\n")
        if (idx + 1) % 100 == 0 or idx + 1 == len(lines):
            f.flush()
            print(f"  {idx+1}/{len(lines)}  {time.time()-t0:.1f}s  REAL={nreal} NOTREAL={nnot} INC={ninc}", flush=True)
print(f"DONE: REAL={nreal} NOTREAL={nnot} INCONCLUSIVE={ninc}  ({time.time()-t0:.1f}s) -> {OUT}", flush=True)
