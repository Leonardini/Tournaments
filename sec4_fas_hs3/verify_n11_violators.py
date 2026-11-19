#!/usr/bin/env python3
"""The violators of FAS = HS3 on 11 vertices, and the minimum 3-cycle hitting sets of T*.

Backs two statements of the paper:

 (1) Section 4: among all tournaments on 11 vertices exactly 12 (up to isomorphism) have
     HS3 < FAS; 6 of them are self-converse (Table B.1), the other 6 form 3 converse pairs,
     exactly one is regular (it is T*), and all 12 are 3-inducible.
     The list n11_violators.txt is the output of sweep_n11_strong.sh, which runs hs3fas.c on
     every strong tournament on 11 vertices (a long run). A tournament that is not strong has
     FAS and HS3 equal to the sums over its strong components, which have at most 10 vertices,
     where FAS = HS3 (Theorem 4.1); so the strong ones are all that can violate.
     This script checks the 12 listed tournaments: each is a strong tournament with
     HS3 = FAS - 1 (FAS by a Held-Karp DP, HS3 by CP-SAT), no two are isomorphic, the
     self-converse / converse-pair / regular counts above, the regular one is isomorphic to
     T*, and each is induced by three voters (CP-SAT, profile rechecked).

 (2) Appendix C: every minimum 3-cycle hitting set of T* contains the nine arcs from
     {4,5,6} to {8,9,10}, and there are exactly nine such sets (CP-SAT enumerates all).

Every guaranteed step asserts. Usage: python3 verify_n11_violators.py   (a few seconds)
"""
import os
import re
from itertools import combinations, permutations

from ortools.sat.python import cp_model

HERE = os.path.dirname(os.path.abspath(__file__))
N = 11
# The counts the paper states; recomputed below, and the script fails if any differs.
PAPER_VIOLATORS, PAPER_SELF_CONVERSE, PAPER_REGULAR = 12, 6, 1
PAPER_TSTAR_HS3_SETS = 9


def from_bits(bits):
    """Upper-triangle row-major bits, '1' iff i -> j (i < j); vertices 0..n-1."""
    assert len(bits) == N * (N - 1) // 2, "wrong bit-string length"
    adj = [[False] * N for _ in range(N)]
    k = 0
    for i in range(N):
        for j in range(i + 1, N):
            if bits[k] == "1":
                adj[i][j] = True
            else:
                adj[j][i] = True
            k += 1
    return adj


def tstar_from_r():
    """T* from the three voters in tstar_voters.R (the single place they are stated)."""
    src = open(os.path.join(HERE, "tstar_voters.R")).read()
    block = src[src.index("tstar_voters = list("):src.index("majority_matrix")]
    voters = [[int(x) - 1 for x in v.split(",")] for v in re.findall(r"c\(([^)]*)\)", block)]
    assert len(voters) == 3 and all(sorted(v) == list(range(N)) for v in voters)
    return majority(voters)


def majority(voters):
    pos = [{v: i for i, v in enumerate(o)} for o in voters]
    adj = [[False] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            if a != b and 2 * sum(p[a] < p[b] for p in pos) > len(voters):
                adj[a][b] = True
    return adj


def arcs(adj):
    return [(a, b) for a in range(N) for b in range(N) if adj[a][b]]


def is_strong(adj):
    def reach(s, fwd):
        seen, stack = {s}, [s]
        while stack:
            u = stack.pop()
            for v in range(N):
                if v not in seen and (adj[u][v] if fwd else adj[v][u]):
                    seen.add(v); stack.append(v)
        return seen
    return len(reach(0, True)) == N and len(reach(0, False)) == N


def fas(adj):
    """Held-Karp: fewest backward arcs over all linear orders."""
    out = [sum(1 << v for v in range(N) if adj[u][v]) for u in range(N)]
    best = [0] + [None] * ((1 << N) - 1)
    for S in range(1, 1 << N):
        best[S] = min(best[S ^ (1 << v)] + bin((S ^ (1 << v)) & out[v]).count("1")
                      for v in range(N) if S >> v & 1)   # v placed last: its arcs into S are backward
    return best[-1]


def cyclic_triangles(adj):
    return [t for t in combinations(range(N), 3)
            if all(sum(adj[x][y] for y in t) == 1 for x in t)]


def hs3_model(adj):
    A = arcs(adj)
    idx = {a: i for i, a in enumerate(A)}
    m = cp_model.CpModel()
    x = [m.NewBoolVar(f"x{i}") for i in range(len(A))]
    for t in cyclic_triangles(adj):
        m.AddBoolOr([x[idx[(a, b)]] for a in t for b in t if adj[a][b]])
    return m, x, A


def hs3(adj):
    m, x, _ = hs3_model(adj)
    m.Minimize(sum(x))
    s = cp_model.CpSolver(); s.parameters.num_workers = 1
    assert s.Solve(m) == cp_model.OPTIMAL, "HS3 model is feasible and bounded by construction"
    return round(s.ObjectiveValue())


def all_min_hs3(adj, size):
    m, x, A = hs3_model(adj)
    m.Add(sum(x) <= size)

    class Collect(cp_model.CpSolverSolutionCallback):
        def __init__(self):
            super().__init__(); self.sols = []

        def on_solution_callback(self):
            self.sols.append(frozenset(A[i] for i in range(len(A)) if self.Value(x[i])))

    s = cp_model.CpSolver(); s.parameters.enumerate_all_solutions = True
    s.parameters.num_workers = 1
    cb = Collect()
    assert s.Solve(m, cb) == cp_model.OPTIMAL, "enumeration must finish"
    return cb.sols


def three_voters(adj):
    """Three linear orders with every arc forward in at least two (CP-SAT), or None."""
    m = cp_model.CpModel()
    pos = [[m.NewIntVar(0, N - 1, "") for _ in range(N)] for _ in range(3)]
    for p in pos:
        m.AddAllDifferent(p)
    for a, b in arcs(adj):
        f = [m.NewBoolVar("") for _ in range(3)]
        for k in range(3):
            m.Add(pos[k][a] < pos[k][b]).OnlyEnforceIf(f[k])
            m.Add(pos[k][a] > pos[k][b]).OnlyEnforceIf(f[k].Not())
        m.Add(sum(f) >= 2)
    s = cp_model.CpSolver(); s.parameters.num_workers = 1
    if s.Solve(m) not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return None
    return [sorted(range(N), key=lambda v: s.Value(pos[k][v])) for k in range(3)]


def isomorphic(g, h):
    """Backtracking isomorphism test, vertices matched by (out-degree, in-neighbourhood scores)."""
    def sig(adj):
        sc = [sum(r) for r in adj]
        return [(sc[v], tuple(sorted(sc[u] for u in range(N) if adj[u][v]))) for v in range(N)]
    sg, sh = sig(g), sig(h)
    if sorted(sg) != sorted(sh):
        return False
    order = sorted(range(N), key=lambda v: sum(s == sg[v] for s in sg))
    f, used = {}, set()

    def extend(i):
        if i == N:
            return True
        v = order[i]
        for w in range(N):
            if w in used or sh[w] != sg[v]:
                continue
            if all(g[v][u] == h[w][f[u]] for u in f):
                f[v] = w; used.add(w)
                if extend(i + 1):
                    return True
                del f[v]; used.discard(w)
        return False
    return extend(0)


def converse(adj):
    return [[adj[b][a] for b in range(N)] for a in range(N)]


def main():
    lines = [l.strip() for l in open(os.path.join(HERE, "n11_violators.txt")) if l.strip()]
    T = [from_bits(b) for b in lines]
    assert len(T) == PAPER_VIOLATORS, f"{len(T)} violators listed, paper says {PAPER_VIOLATORS}"
    for i, t in enumerate(T):
        assert is_strong(t), f"violator {i + 1} is not strong"
        f, h = fas(t), hs3(t)
        assert h == f - 1, f"violator {i + 1}: FAS {f}, HS3 {h}"
        prof = three_voters(t)
        assert prof is not None and majority(prof) == t, f"violator {i + 1} not 3-inducible"
        print(f"violator {i + 1:2d}: strong, FAS = {f}, HS3 = {h}, 3-inducible")
    for i, j in combinations(range(len(T)), 2):
        assert not isomorphic(T[i], T[j]), f"violators {i + 1} and {j + 1} are isomorphic"
    sc = [i for i, t in enumerate(T) if isomorphic(t, converse(t))]
    pairs = [(i, j) for i, j in combinations(range(len(T)), 2) if isomorphic(T[i], converse(T[j]))]
    assert len(sc) == PAPER_SELF_CONVERSE, f"{len(sc)} self-converse"
    assert 2 * len(pairs) + len(sc) == len(T), "the others do not form converse pairs"
    reg = [i for i, t in enumerate(T) if all(2 * sum(r) == N - 1 for r in t)]
    assert len(reg) == PAPER_REGULAR, f"{len(reg)} regular"
    tstar = tstar_from_r()
    assert isomorphic(T[reg[0]], tstar), "the regular violator is not T*"
    assert reg[0] in sc
    print(f"{len(T)} pairwise non-isomorphic violators: {len(sc)} self-converse, "
          f"{len(pairs)} converse pairs, {len(reg)} regular (isomorphic to T*)")

    # (2) minimum 3-cycle hitting sets of T* (manuscript labels: vertex v is v - 1 here)
    h = hs3(tstar)
    sols = all_min_hs3(tstar, h)
    A1, B1 = {3, 4, 5}, {7, 8, 9}
    cross = {(a, b) for a, b in arcs(tstar) if (a in A1 and b in B1) or (a in B1 and b in A1)}
    assert len(cross) == 9 and all(a in A1 for a, _ in cross), "{4,5,6} -> {8,9,10} is a module arc"
    assert len(sols) == PAPER_TSTAR_HS3_SETS, f"{len(sols)} minimum hitting sets"
    assert all(cross <= S for S in sols), "a minimum hitting set misses an arc 4,5,6 -> 8,9,10"
    print(f"T*: HS3 = {h}; all {len(sols)} minimum 3-cycle hitting sets contain the nine arcs "
          "from {4,5,6} to {8,9,10}")
    print("PASS")


if __name__ == "__main__":
    main()
