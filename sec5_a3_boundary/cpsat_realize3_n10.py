#!/usr/bin/env python3
# cpsat_realize3_n10.py INMFILE GIDXFILE [LIMIT] — INDEPENDENT (OR-Tools CP-SAT, position-var + AllDifferent
# encoding) 3-realizability check for n=10 tournaments, to cross-check the CPLEX pairwise-encoding ILP.
# INFEASIBLE here + NOTREAL in CPLEX = two independent proofs of non-3-realizability. Reads inm[v] bitmasks.
import sys
from ortools.sat.python import cp_model
n = 10
inm_lines = open(sys.argv[1]).read().split("\n")
gidx = open(sys.argv[2]).read().split("\n")
LIMIT = int(sys.argv[3]) if len(sys.argv) > 3 else len(inm_lines)

def check(inm, k=3):
    A = [[1 if (inm[v] >> u) & 1 else 0 for v in range(n)] for u in range(n)]
    arcs = [(u, v) for u in range(n) for v in range(n) if A[u][v] == 1]
    maj = (k + 1) // 2
    m = cp_model.CpModel()
    pos = [[m.NewIntVar(0, n - 1, f"p{p}_{v}") for v in range(n)] for p in range(k)]
    for p in range(k): m.AddAllDifferent(pos[p])
    bef = {}
    for p in range(k):
        for (u, v) in arcs:
            b = m.NewBoolVar(f"b{p}_{u}_{v}")
            m.Add(pos[p][u] < pos[p][v]).OnlyEnforceIf(b)
            m.Add(pos[p][u] > pos[p][v]).OnlyEnforceIf(b.Not())
            bef[(p, u, v)] = b
    for (u, v) in arcs:
        m.Add(sum(bef[(p, u, v)] for p in range(k)) >= maj)
    s = cp_model.CpSolver(); s.parameters.num_search_workers = 2
    st = s.Solve(m)
    return {cp_model.OPTIMAL: "FEASIBLE", cp_model.FEASIBLE: "FEASIBLE",
            cp_model.INFEASIBLE: "INFEASIBLE", cp_model.UNKNOWN: "UNKNOWN"}[st]

ninf = 0; nfeas = 0
for i in range(min(LIMIT, len(inm_lines))):
    if not inm_lines[i].strip(): continue
    inm = [int(x) for x in inm_lines[i].split()]
    r = check(inm, 3)
    if r == "INFEASIBLE": ninf += 1
    else: nfeas += 1
    print(f"  gidx {gidx[i]}: k=3 CP-SAT -> {r}")
print(f"SUMMARY: {ninf} INFEASIBLE (not 3-real), {nfeas} feasible/unknown  (expect all INFEASIBLE)")
