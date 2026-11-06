#!/usr/bin/env python3
r"""
All minimal obstacle supports of a tournament, by exact vertex enumeration of its optimal-dual face.

T is a tournament with arc set A, alpha = alpha*(T) its predictability (exact). The optimal-dual face is
    F = { y >= 0 : sum y = 1,  fwd_pi(y) <= alpha  for every order pi },
a polytope.  For S subset of A, the optimal duals supported inside S form F cap {y_e = 0, e not in S}, a face
of F.  Hence: every inclusion-minimal support S of an optimal dual is the support of a vertex of F; the
minimal supports are exactly the inclusion-minimal sets among the vertex supports; and the optimal dual on
a minimal support S is unique iff exactly one vertex of F has support S (a larger face has >= 2 vertices,
all with support S by minimality).

Steps (each exact; a failure of a promised step raises):
  1. alpha exactly (obstacle_lp.compute_alpha: float cutting plane, exact LP on the collected orders, exact
     Held-Karp check of its y).
  2. E* = the union of the supports of all optimal duals, from one exact LP over the cone of optimal duals:
        max sum_e s_e  s.t.  0 <= s_e <= 1,  s_e <= y_e,  y >= 0,  fwd_pi(y) <= alpha sum(y)  (all pi).
     The cone is closed under addition and scaling, so the optimum is |E*| and any optimal y has support E*.
     Orders are collected by a float cutting plane, then the LP over them is solved exactly and its y is
     checked against all orders by integer Held-Karp (a verified y makes the relaxed optimum the true one).
  3. Vertex enumeration of F in the coordinates E* by cddlib (exact rational double description, after
     recognising the implicit equalities), with the collected orders as rows.  Every vertex is checked exactly against all 9! orders by integer Held-Karp; violated orders are
     added and the enumeration rerun.  When every vertex passes, the relaxed polytope (= conv of its vertices) lies in F,
     and contains F, so it is F.
Output per tournament: alpha, |E*|, the vertices (exact), and the minimal supports with their unique duals.

Usage: python3 face_vertices.py <tournaments.txt> <out.jsonl> <k> <K> [indices.txt]
"""
import sys, json, time
import cdd, cdd.gmp
from fractions import Fraction
from math import lcm
import obstacle_lp as MS



def support_union(T, alpha, rows):
    m = T.m; nv = 2 * m                                  # (y_0..y_{m-1}, s_0..s_{m-1})
    obj = [0] * m + [1] * m

    def le_rows(exact):
        out = []
        for e in range(m):
            r = [0] * nv; r[m + e] = 1; r[e] = -1; out.append((r, 0))          # s_e <= y_e
            r = [0] * nv; r[m + e] = 1; out.append((r, 1))                       # s_e <= 1
            r = [0] * nv; r[m + e] = -1; out.append((r, 0))                      # s_e >= 0
            r = [0] * nv; r[e] = -1; out.append((r, 0))                          # y_e >= 0
        for F in rows:
            Fs = set(F)
            a = [((1 if e in Fs else 0) - alpha) for e in range(m)] + [0] * m
            out.append(([float(c) for c in a] if not exact else a, 0))
        return out
    lb = [0.0] * nv; ub = [1e4] * m + [1.0] * m
    af = float(alpha)
    for _ in range(10000):                               # float proposal of the relevant orders
        sol = MS.float_lp(nv, obj, le_rows(False), [], lb, ub)
        assert sol is not None
        val, order = T.best_float(sol[:m])
        if val <= af * sum(sol[:m]) + 1e-7:
            break
        F = MS.fwd_set(order, T.arcs)
        if F in rows:
            break
        rows.append(F)
    while True:
        st, val, x, _ = MS.exact_lp(nv, obj, le_rows(True), [])
        assert st == "optimal", "support-union LP is feasible (y = 0) and bounded (s <= 1)"
        y = x[:m]
        best, order = T.best_exact(y)
        if best <= alpha * sum(y):
            E = [e for e in range(m) if y[e] > 0]
            assert len(E) == val, "optimal value must equal the size of the support union"
            return E
        F = MS.fwd_set(order, T.arcs)
        assert F not in rows
        rows.append(F)


def face_vertices_exact(E, rowsE, alpha):
    """vertices of {y in R^E : y >= 0, sum y = 1, sum_{e in R} y_e <= alpha for R in rowsE}, exact.
    cddlib (rationals): implicit equalities are recognised first (matrix_canonicalize_linearity), which keeps
    the double description fast on these very degenerate faces; then the generators are computed."""
    k = len(E); p, q = alpha.numerator, alpha.denominator
    H = [[Fraction(0)] + [Fraction(1 if j == i else 0) for j in range(k)] for i in range(k)]
    for R in rowsE:
        Rs = set(R)
        H.append([Fraction(p)] + [Fraction(-q if j in Rs else 0) for j in range(k)])
    H.append([Fraction(-1)] + [Fraction(1)] * k)
    M = cdd.gmp.matrix_from_array(H, lin_set={len(H) - 1}, rep_type=cdd.RepType.INEQUALITY)
    cdd.gmp.matrix_canonicalize_linearity(M)
    V = cdd.gmp.copy_generators(cdd.gmp.polyhedron_from_matrix(M))
    assert not V.lin_set, "the face is a polytope: no lines"
    verts = []
    for r in V.array:
        assert r[0] == 1, "the face is a polytope: no rays"
        verts.append([Fraction(v) for v in r[1:]])
    assert verts, "no vertex reported for a nonempty polytope"
    return verts


def face(T, log):
    rows = []
    alpha = MS.compute_alpha(T, False, rows)
    E = support_union(T, alpha, rows)
    pos = {e: i for i, e in enumerate(E)}
    def restrict(F):
        return tuple(sorted(pos[e] for e in F if e in pos))
    rowsE = sorted({restrict(F) for F in rows})
    rounds = 0
    while True:
        rounds += 1
        verts = face_vertices_exact(E, rowsE, alpha)
        bad = set()
        for v in verts:
            y = [Fraction(0)] * T.m
            for i, e in enumerate(E):
                y[e] = v[i]
            best, order = T.best_exact(y)
            if best > alpha:
                bad.add(restrict(MS.fwd_set(order, T.arcs)))
            else:
                assert best == alpha
        if not bad:
            break
        assert not (bad & set(rowsE)), "a vertex violates a row the enumeration was given"
        rowsE = sorted(set(rowsE) | bad)
    full = []
    for v in verts:
        y = [Fraction(0)] * T.m
        for i, e in enumerate(E):
            y[e] = v[i]
        full.append(y)
    sups = [frozenset(e for e in range(T.m) if y[e] > 0) for y in full]
    minimal = sorted({S for S in sups if not any(S2 < S for S2 in sups)}, key=lambda S: (len(S), sorted(S)))
    out = []
    for S in minimal:
        ys = [y for y, S2 in zip(full, sups) if S2 == S]
        out.append({"arcs": [list(T.arcs[e]) for e in sorted(S)], "y": [str(ys[0][e]) for e in sorted(S)],
                    "n_vertices": len(ys)})
    return alpha, E, full, out, {"rows": len(rowsE), "rounds": rounds, "n_vertices": len(full)}


def main():
    src, outp, k, K = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    ts = MS.read_tournaments(src)
    hk = MS.HK(len(ts[0]))
    if len(sys.argv) > 5:
        idxs = [int(x) for x in open(sys.argv[5]).read().split()]
        mine = [i for j, i in enumerate(idxs) if j % K == k]
    else:
        mine = [i for i in range(len(ts)) if i % K == k]
    t0 = time.time()
    log = lambda s: (sys.stderr.write(f"{time.strftime('%H:%M:%S')} [{time.time() - t0:7.0f}s] worker {k}/{K} {s}\n"),
                     sys.stderr.flush())
    with open(outp, "w") as fh:
        for done, idx in enumerate(mine, 1):
            t1 = time.time()
            T = MS.Tour(ts[idx], hk)
            alpha, E, verts, sups, stats = face(T, log)
            fh.write(json.dumps({"idx": idx, "alpha": str(alpha), "E": len(E), "supports": sups,
                                 "vertices": [[str(v) for v in y] for y in verts], **stats,
                                 "seconds": round(time.time() - t1, 2)}) + "\n"); fh.flush()
            if done % 10 == 0 or done == len(mine) or time.time() - t1 > 60:
                el = time.time() - t0
                log(f"{done}/{len(mine)} done (last: idx {idx}, {stats['n_vertices']} vertices, "
                    f"{time.time() - t1:.1f}s), ETA {el / done * (len(mine) - done):.0f}s")


if __name__ == "__main__":
    main()
