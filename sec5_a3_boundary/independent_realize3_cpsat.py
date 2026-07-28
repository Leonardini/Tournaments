#!/usr/bin/env python3
# Independent 3-realizability check of allGraphs[[1068]] via OR-Tools CP-SAT (different SOLVER than the
# CPLEX realize_k.py) and a different ENCODING (position variables + AllDifferent + reified order, not
# pairwise y_uv + transitivity triples). Adjacency hardcoded from the verified printout (A[i][j]=1 => i->j,
# 0-indexed). INFEASIBLE here + infeasible in CPLEX = two independent proofs it is not 3-realizable.
from ortools.sat.python import cp_model

rows = ["01111100000","00110100011","00011100110","00001110011","01000011101",
        "00001001111","11100101000","11110000010","11010011000","10001010101","10100011100"]
n = len(rows)
A = [[int(c) for c in r] for r in rows]
assert all(len(r) == n for r in A)
assert all(A[i][i] == 0 for i in range(n)), "diagonal must be 0"
assert all(A[i][j] + A[j][i] == 1 for i in range(n) for j in range(n) if i != j), "not a tournament"
assert all(sum(A[i]) == 5 for i in range(n)), "not out-regular deg 5"
arcs = [(i, j) for i in range(n) for j in range(n) if A[i][j] == 1]
print(f"n={n}, arcs={len(arcs)} (=C(11,2)={n*(n-1)//2}), out-regular deg-5 tournament: OK")

for k in (3, 5):
    maj = (k + 1) // 2
    m = cp_model.CpModel()
    pos = [[m.NewIntVar(0, n - 1, f"pos_{p}_{v}") for v in range(n)] for p in range(k)]
    for p in range(k):
        m.AddAllDifferent(pos[p])                       # voter p is a permutation (linear order)
    before = {}
    for p in range(k):
        for (u, v) in arcs:
            b = m.NewBoolVar(f"bef_{p}_{u}_{v}")        # b <=> voter p ranks u before v
            m.Add(pos[p][u] < pos[p][v]).OnlyEnforceIf(b)
            m.Add(pos[p][u] > pos[p][v]).OnlyEnforceIf(b.Not())
            before[(p, u, v)] = b
    for (u, v) in arcs:                                 # arc u->v: >= maj voters rank u before v
        m.Add(sum(before[(p, u, v)] for p in range(k)) >= maj)
    solver = cp_model.CpSolver(); solver.parameters.num_search_workers = 2
    st = solver.Solve(m)
    name = {cp_model.OPTIMAL: "FEASIBLE", cp_model.FEASIBLE: "FEASIBLE",
            cp_model.INFEASIBLE: "INFEASIBLE (proven)", cp_model.UNKNOWN: "UNKNOWN"}[st]
    print(f"  k={k} (maj>={maj}): {name}  [{solver.StatusName(st)}, {solver.WallTime():.2f}s]")
