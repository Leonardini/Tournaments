#!/usr/bin/env python3
"""Appendix (circulant family): the fewest voters giving every arc exactly 2/3 of the votes is not
preserved by lifting.

In a profile of k voters (3 | k) in which every arc is forward in exactly 2k/3 voters, every arc is
backward in exactly k/3, so every cyclic triangle gets k backward incidences, at least one per voter:
every voter is admissible (one backward arc on every cyclic triangle). This script
  (1) shows by CP-SAT that on Z_81 the admissible orders of the circulants of e = (1, 25, 55) and of
      e' = (55, 7, 19), the lift (Lemma cf-lift) of the 27-vertex circulant of (1, 7, 19), are exactly
      the progressions: an admissible order that is not one is INFEASIBLE (and, as a control, the model
      without that requirement is feasible and returns a progression);
  (2) finds, among progressions (hence among all profiles, by (1) and, at 27, by circulant_bases.py),
      the least k in {3, 6, 9, ...} with every arc forward in exactly 2k/3 voters:
      9 at 27 vertices, 9 for (1, 25, 55) on 81, and 15 for the lift on 81.
Every profile found is rechecked arc by arc. Every guaranteed step asserts.
Usage: python3 circulant81_voter_minimum.py     (about a minute)
"""
from ortools.sat.python import cp_model

PAPER_MINIMUM = {(27, (1, 7, 19)): 9, (81, (1, 25, 55)): 9, (81, (55, 7, 19)): 15}


def circulant(n, e):
    assert sum(e) % n == 0 and len(set(e)) == 3
    S = {s for s in range(1, n) if sum(s * x % n for x in e) == n}
    assert all((s in S) != ((n - s) in S) for s in range(1, n)), "not a tournament"
    return S, [pow(x, -1, n) for x in e]


def nonprogression_admissible(n, e, exclude):
    S, D = circulant(n, e)
    arc = lambda u, v: (v - u) % n in S
    tri = [(u, v, w) for u in range(n) for v in range(n) for w in range(n)
           if u < v and u < w and arc(u, v) and arc(v, w) and arc(w, u)]
    assert len(tri) == n * (n * n - 1) // 24, "a regular tournament has n(n^2-1)/24 cyclic triangles"
    m = cp_model.CpModel(); p = [m.NewIntVar(0, n - 1, "") for _ in range(n)]
    m.AddAllDifferent(p); m.Add(p[0] == 0)                 # rotation is an automorphism
    b = {}
    for u in range(n):
        for v in range(n):
            if arc(u, v):
                b[u, v] = m.NewBoolVar("")
                m.Add(p[v] < p[u]).OnlyEnforceIf(b[u, v]); m.Add(p[v] > p[u]).OnlyEnforceIf(b[u, v].Not())
    for u, v, w in tri:
        m.Add(b[u, v] + b[v, w] + b[w, u] == 1)
    if exclude:
        for d in D:
            lits = [m.NewBoolVar("") for _ in range(1, n)]
            for k, x in zip(range(1, n), lits):
                m.Add(p[k * d % n] != k).OnlyEnforceIf(x)
            m.AddBoolOr(lits)
    sv = cp_model.CpSolver(); sv.parameters.num_workers = 1
    st = sv.Solve(m)
    assert st in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.INFEASIBLE), "CP-SAT must decide"
    if st == cp_model.INFEASIBLE:
        return None
    order = sorted(range(n), key=lambda v: sv.Value(p[v]))
    return any(order == [k * d % n for k in range(n)] for d in D)


def least_voters(n, e):
    S, D = circulant(n, e)
    cols = [(i, a) for i in range(3) for a in range(n)]
    for k in range(3, 3 * n + 1, 3):                      # k = 3n always works (equal weights)
        m = cp_model.CpModel(); y = [m.NewIntVar(0, k, "") for _ in cols]; m.Add(sum(y) == k)
        for s in S:
            for v in range(n):
                m.Add(sum(y[j] for j, (i, a) in enumerate(cols) if (v - a) * e[i] % n < s * e[i] % n) == k // 3)
        sv = cp_model.CpSolver(); sv.parameters.num_workers = 1
        st = sv.Solve(m)
        assert st in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.INFEASIBLE), "CP-SAT must decide"
        if st != cp_model.INFEASIBLE:
            prof = [[(a + t * D[i]) % n for t in range(n)]
                    for j, (i, a) in enumerate(cols) for _ in range(sv.Value(y[j]))]
            pos = [{v: t for t, v in enumerate(o)} for o in prof]
            assert len(prof) == k and all(sum(q[u] < q[(u + s) % n] for q in pos) == 2 * k // 3
                                          for u in range(n) for s in S), "profile recheck"
            return k
    raise AssertionError("3n equally weighted progressions always give every arc 2/3")


for (n, e), want in PAPER_MINIMUM.items():
    if n == 81:
        assert nonprogression_admissible(n, e, exclude=False) is True, "control: a progression is admissible"
        assert nonprogression_admissible(n, e, exclude=True) is None, f"{e}: an admissible non-progression"
        print(f"n = {n}, e = {e}: the admissible orders are exactly the progressions", flush=True)
    k = least_voters(n, e)
    assert k == want, f"n = {n}, e = {e}: least k = {k}, paper says {want}"
    print(f"n = {n}, e = {e}: fewest voters giving every arc exactly 2/3 = {k}", flush=True)
print("PASS")
