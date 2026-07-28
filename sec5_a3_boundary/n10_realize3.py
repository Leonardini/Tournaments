#!/usr/bin/env python3
# n10_realize3.py CHUNK.tin OUT.csv — decide 3-realizability of each n=10 tournament in CHUNK.tin.
# Each input line: "gidx inm0 ... inm9" (gidx = global 0-based catalogue index; inm[v] = in-neighbour bitmask,
# arc u->v iff bit u of inm[v]). k=3 majority ILP (3 orders, every arc forward in >= 2). FEASIBLE => REAL;
# proven infeasible => NOTREAL; else INCONCLUSIVE. Writes "gidx,verdict" per line. SINGLE THREAD.
import sys, cplex, time
IN, OUT = sys.argv[1], sys.argv[2]
n, k, maj = 10, 3, 2
pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
triples = [(u, v, w) for u in range(n) for v in range(u + 1, n) for w in range(v + 1, n)]
# static constraint template (transitivity) built once; arc-coverage rebuilt per tournament
def base_model():
    cpx = cplex.Cplex()
    for s in (cpx.set_results_stream, cpx.set_log_stream, cpx.set_warning_stream): s(None)
    yidx = {}; t = 0
    for p in range(k):
        for (u, v) in pairs: yidx[(p, u, v)] = t; t += 1
    return cpx, yidx, t

def solve(inm):
    A = [[1 if (inm[v] >> u) & 1 else 0 for v in range(n)] for u in range(n)]
    cpx, yidx, t = base_model()
    cpx.variables.add(types=["B"] * t)
    R = []; S = []; H = []
    for p in range(k):
        for (u, v, w) in triples:
            ind = [yidx[(p, u, v)], yidx[(p, v, w)], yidx[(p, u, w)]]
            R.append(cplex.SparsePair(ind, [1, 1, -1])); S.append("L"); H.append(1.0)
            R.append(cplex.SparsePair(ind, [1, 1, -1])); S.append("G"); H.append(0.0)
    for (u, v) in pairs:
        ind = [yidx[(p, u, v)] for p in range(k)]
        if A[u][v] == 1: R.append(cplex.SparsePair(ind, [1] * k)); S.append("G"); H.append(2.0)
        else:            R.append(cplex.SparsePair(ind, [1] * k)); S.append("L"); H.append(1.0)
    cpx.linear_constraints.add(lin_expr=R, senses=S, rhs=H)
    cpx.parameters.threads.set(1); cpx.parameters.timelimit.set(120)
    cpx.solve()
    sts = cpx.solution.get_status_string(); feas = cpx.solution.is_primal_feasible()
    return "REAL" if feas else ("NOTREAL" if "infeasible" in sts.lower() else "INCONCLUSIVE")

t0 = time.time(); nreal = nnot = ninc = 0
with open(OUT, "w") as f:
    for lno, line in enumerate(open(IN)):
        toks = line.split()
        if not toks: continue
        gidx = toks[0]; inm = [int(x) for x in toks[1:]]
        v = solve(inm)
        nreal += v == "REAL"; nnot += v == "NOTREAL"; ninc += v == "INCONCLUSIVE"
        f.write(f"{gidx},{v}\n")
        if (lno + 1) % 20000 == 0:
            f.flush()
            print(f"  {IN}: {lno+1} done  REAL={nreal} NOTREAL={nnot} INC={ninc}  {time.time()-t0:.0f}s", flush=True)
print(f"DONE {IN}: REAL={nreal} NOTREAL={nnot} INC={ninc}  ({time.time()-t0:.1f}s) -> {OUT}", flush=True)
