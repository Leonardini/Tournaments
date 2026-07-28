#!/usr/bin/env python3
# (E) Explicit 5-voter realization of the A(3) counterexample allGraphs[[1068]] (McG=5 witness), verified.
# (D) 3-realizability of its single-vertex deletion (n=10). It is C_11 vertex-transitive => all 11
#     deletions isomorphic, so one check decides: smaller n=10 counterexample vs. vertex-critical at n=11.
from ortools.sat.python import cp_model

rows = ["01111100000","00110100011","00011100110","00001110011","01000011101",
        "00001001111","11100101000","11110000010","11010011000","10001010101","10100011100"]
A = [[int(c) for c in r] for r in rows]; N = len(A)

def realizable(sub, k):
    """sub = list of kept vertices; try to realize induced subtournament by k voters. Return (feasible, perms)."""
    idx = {v: i for i, v in enumerate(sub)}; n = len(sub); maj = (k + 1) // 2
    arcs = [(idx[u], idx[v]) for u in sub for v in sub if u != v and A[u][v] == 1]
    m = cp_model.CpModel()
    pos = [[m.NewIntVar(0, n - 1, f"p{p}_{v}") for v in range(n)] for p in range(k)]
    for p in range(k): m.AddAllDifferent(pos[p])
    bef = {}
    for p in range(k):
        for (u, v) in arcs:
            b = m.NewBoolVar(f"b{p}_{u}_{v}")
            m.Add(pos[p][u] < pos[p][v]).OnlyEnforceIf(b)
            m.Add(pos[p][u] > pos[p][v]).OnlyEnforceIf(b.Not()); bef[(p, u, v)] = b
    for (u, v) in arcs: m.Add(sum(bef[(p, u, v)] for p in range(k)) >= maj)
    s = cp_model.CpSolver(); s.parameters.num_search_workers = 2; st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        perms = []
        for p in range(k):
            order = sorted(range(n), key=lambda v: s.Value(pos[p][v]))  # earliest-first
            perms.append([sub[v] for v in order])                       # in ORIGINAL vertex labels
        return True, perms
    return False, None

# ---------- (E) 5-voter realization of the full tournament ----------
full = list(range(N))
ok5, perms = realizable(full, 5)
print(f"(E) full n=11: 5-realizable = {ok5}  => McG = 5 (not 3, but 5)")
if ok5:
    print("    5 voters (earliest-ranked vertex first, 0-based labels):")
    for i, pm in enumerate(perms): print(f"      voter {i+1}: {pm}")
    # independent verification: every arc forward in >= 3 of the 5
    bad = 0
    for u in range(N):
        for v in range(N):
            if A[u][v] == 1:
                cnt = sum(pm.index(u) < pm.index(v) for pm in perms)
                if cnt < 3: bad += 1
    print(f"    verification: arcs with < 3 voters agreeing = {bad}  (0 => valid realization)")

# ---------- (D) is the n=10 deletion 3-realizable? (VT => delete vertex 0 WLOG) ----------
sub10 = [v for v in range(N) if v != 0]
ok3_10, _ = realizable(sub10, 3)
print(f"\n(D) delete 1 vertex (n=10, unique up to iso since VT): 3-realizable = {ok3_10}")
if ok3_10:
    print("    => 3-realizable after ANY single deletion: allGraphs[[1068]] is VERTEX-CRITICAL for non-3-realizability.")
else:
    print("    => NOT 3-realizable at n=10: a SMALLER (n=10) counterexample lives inside it! (check its alpha*)")
