#!/usr/bin/env python3
"""Catalogue of the minimal obstacles at n = 9, from the exact face enumerations.

Inputs (this folder): face1054_*.jsonl and face16620_*.jsonl (face_vertices.py on the1054.txt and
g8set_16620.txt) and face254_*.jsonl (face_signed.py on margin1_254.txt).

An obstacle class is an isomorphism class of minimal supports carrying their (unique) optimal dual, as a
multidigraph: arc u -> v with multiplicity m, the dual weight of an arc being its multiplicity divided by
the total. For the signed duals of the 254, a negative multiplicity marks an arc with negative weight, and
the weight is the multiplicity divided by sum_mult, the signed sum (total_mult is the sum of absolute values).

Numbering: the classes met among the 1,054 tournaments without G8 are O01, O02, ... in order of alpha*,
then number of arcs, then decreasing number of tournaments, then the first tournament (in input order)
in which the class occurs, then canonical form; G8 is the class of the
8-vertex obstacle; the classes met only among the 16,620 tournaments containing G8 follow, in order of
alpha*, number of arcs, total multiplicity, first tournament, canonical form. The signed classes of the 254 are U01, U02,
... in order of alpha^=, number of arcs, decreasing number of tournaments, first tournament, canonical form.

Checks (each a hard failure): every input tournament appears exactly once; every minimal support carries
exactly one vertex of its face (so its dual is unique); every tournament of the 16,620 with alpha* = 13/20
has only copies of G8 as minimal obstacles; every class is Eulerian as a multidigraph (in- and out-
multiplicity agree at each vertex).

Output: n9_minimal_obstacles.tsv and n9_signed_obstacles_254.tsv, and a summary on stdout.
"""
import glob, json, sys
from fractions import Fraction
from collections import Counter, defaultdict
from math import lcm, gcd
from functools import reduce
import igraph as ig


def canon(arcs, labels):
    """canonical string of a digraph with integer arc labels (vertices = those touched by arcs): each arc
    u -> v with label c becomes u -> w -> v with the new vertex w coloured by c; original vertices share one
    colour; bliss (igraph) gives the canonical labelling.  igraph 1.0: labeling[i] is the ORIGINAL vertex
    placed at canonical position i (the reading checked by selftest_canon; the opposite one is not canonical)."""
    verts = sorted({u for u, _ in arcs} | {v for _, v in arcs})
    pos = {v: i for i, v in enumerate(verts)}
    cols = sorted(set(labels)); cid = {c: i + 1 for i, c in enumerate(cols)}
    n = len(verts); edges = []; colors = [0] * n
    for (u, v), c in zip(arcs, labels):
        w = len(colors); colors.append(cid[c])
        edges += [(pos[u], w), (w, pos[v])]
    g = ig.Graph(n=len(colors), edges=edges, directed=True)
    labeling = g.canonical_permutation(color=colors)
    new = [None] * len(colors)
    for i, o in enumerate(labeling):
        new[o] = i
    E = sorted((new[a], new[b]) for a, b in edges)
    return repr((tuple(cols), n, tuple(colors[o] for o in labeling), tuple(E)))


def selftest_canon():
    """the canonical form must not change under relabelling of vertices and reordering of arcs, and must
    change when one label changes."""
    import random
    rnd = random.Random(7)
    for _ in range(20):
        arcs = [(u, v) if rnd.random() < .5 else (v, u) for u in range(9) for v in range(u + 1, 9) if rnd.random() < .45]
        labs = [rnd.choice([-1, 1, 2, 3]) for _ in arcs]
        forms = set()
        for _ in range(10):
            p = list(range(9)); rnd.shuffle(p); idx = list(range(len(arcs))); rnd.shuffle(idx)
            forms.add(canon([(p[arcs[i][0]], p[arcs[i][1]]) for i in idx], [labs[i] for i in idx]))
        assert len(forms) == 1, "canonical form is not invariant under relabelling"
        assert canon(arcs, [labs[0] + 7] + labs[1:]) not in forms, "canonical form ignores a label"


def mults(ys):
    """the integer multiplicities (coprime) proportional to the rational weights ys (signs kept)."""
    q = [Fraction(v) for v in ys]
    L = reduce(lcm, (v.denominator for v in q)); m = [int(v * L) for v in q]
    g = reduce(gcd, (abs(v) for v in m)); return [v // g for v in m]


def load(pattern, expected):
    recs = [json.loads(l) for p in sorted(glob.glob(pattern)) for l in open(p)]
    idx = sorted(r["idx"] for r in recs)
    assert idx == list(range(expected)), f"{pattern}: {len(idx)} records, expected indices 0..{expected - 1}"
    for r in recs:
        for s in r["supports"]:
            assert s["n_vertices"] == 1, f"{pattern} idx {r['idx']}: a minimal support carries several duals"
    return sorted(recs, key=lambda r: r["idx"])


def classify(recs, signed):
    """classes: canonical key -> dict(arcs, mult, alpha, n_supports, tournaments(set))."""
    cl = {}
    per_t = []
    for r in recs:
        keys = []
        for s in r["supports"]:
            arcs = [tuple(a) for a in s["arcs"]]
            m = mults(s["y"])
            k = canon(arcs, m)
            c = cl.setdefault(k, dict(arcs=arcs, mult=m, alpha=Fraction(r["alpha"]), n_supports=0, tour=set()))
            assert c["alpha"] == Fraction(r["alpha"]), "one class, two values: impossible for an isomorphism class"
            c["n_supports"] += 1; c["tour"].add(r["idx"]); keys.append(k)
        per_t.append(keys)
    return cl, per_t


def describe(c):
    arcs, m = c["arcs"], c["mult"]
    verts = sorted({u for u, _ in arcs} | {v for _, v in arcs})
    ind, outd, bal = Counter(), Counter(), Counter()
    for (u, v), x in zip(arcs, m):
        outd[u] += 1; ind[v] += 1; bal[u] += x; bal[v] -= x
    assert all(bal[v] == 0 for v in verts), "an obstacle that is not Eulerian"
    rk = canon([(v, u) for u, v in arcs], m)
    return dict(alpha=str(c["alpha"]), arcs=len(arcs), verts=len(verts), max_mult=max(abs(x) for x in m),
                total_mult=sum(abs(x) for x in m), sum_mult=sum(m), negative_arcs=sum(x < 0 for x in m),
                n_supports=c["n_supports"], n_tournaments=len(c["tour"]),
                degseq=",".join(f"{outd[v]}/{ind[v]}" for v in sorted(verts, key=lambda v: (outd[v], ind[v]))),
                arclist=";".join(f"{u}>{v}:{x}" for (u, v), x in zip(arcs, m))), rk


def write(path, rows, cols):
    with open(path, "w") as fh:
        fh.write("\t".join(cols) + "\n")
        for r in rows:
            fh.write("\t".join(str(r[c]) for c in cols) + "\n")


def main():
    selftest_canon()
    # ---- standard LP: the 17,674 non-3-inducible 9-tournaments
    r1054 = load("face1054_*.jsonl", 1054)
    r16620 = load("face16620_*.jsonl", 16620)
    c1054, _ = classify(r1054, False)
    c16620, per16620 = classify(r16620, False)
    g8 = [k for k, c in c16620.items() if len({u for a in c["arcs"] for u in a}) == 8]
    assert len(g8) == 1, "exactly one 8-vertex obstacle (G8) expected"
    g8 = g8[0]
    assert c16620[g8]["alpha"] == Fraction(13, 20) and set(c16620[g8]["mult"]) == {1}
    assert g8 not in c1054, "G8 among the 1,054, which by definition do not contain it"
    for r, keys in zip(r16620, per16620):
        if Fraction(r["alpha"]) == Fraction(13, 20):
            assert keys and set(keys) == {g8}, f"idx {r['idx']}: alpha* = 13/20 with an obstacle other than G8"
        else:
            assert Fraction(r["alpha"]) < Fraction(13, 20) and g8 not in keys
    order = sorted(c1054, key=lambda k: (c1054[k]["alpha"], len(c1054[k]["arcs"]), -len(c1054[k]["tour"]),
                                         min(c1054[k]["tour"]), k))
    ids = {k: f"O{j:02d}" for j, k in enumerate(order, 1)}
    ids[g8] = "G8"
    rest = sorted((k for k in c16620 if k not in ids),
                  key=lambda k: (c16620[k]["alpha"], len(c16620[k]["arcs"]), sum(c16620[k]["mult"]),
                                 min(c16620[k]["tour"]), k))
    for j, k in enumerate(rest, len(order) + 1):
        ids[k] = f"O{j:02d}"
    shared = set(c1054) & set(c16620)
    rows = []
    for k in order + [g8] + rest:
        c = c1054.get(k) or c16620[k]
        if k in shared:                                     # a class met in both collections
            c = dict(c, n_supports=c1054[k]["n_supports"] + c16620[k]["n_supports"],
                     tour=c1054[k]["tour"] | {("g", t) for t in c16620[k]["tour"]})
        d, rk = describe(c)
        d.update(id=ids[k], converse=ids.get(rk, "-"),
                 source="1054+16620" if k in shared else ("1054" if k in c1054 else "16620"))
        rows.append(d)
    cols = ["id", "alpha", "arcs", "verts", "max_mult", "total_mult", "n_supports", "n_tournaments", "converse",
            "source", "degseq", "arclist"]
    write("n9_minimal_obstacles.tsv", rows, cols)
    a1054 = Counter(r["alpha"] for r in r1054); a16620 = Counter(r["alpha"] for r in r16620)
    print(f"1,054: {sum(len(r['supports']) for r in r1054)} minimal supports, {len(c1054)} classes; "
          f"{sum(len(r['supports']) > 1 for r in r1054)} tournaments with more than one")
    print(f"16,620: alpha* {sorted(a16620.items(), key=lambda kv: Fraction(kv[0]))}; "
          f"{len(c16620)} classes (G8 + {len(c16620) - 1})")
    print(f"minimum alpha* over the 17,674: {min(Fraction(a) for a in list(a1054) + list(a16620))}")
    print(f"n9_minimal_obstacles.tsv: {len(rows)} classes; self-converse {sum(r['converse'] == r['id'] for r in rows)}; "
          f"shared between the two collections {len(shared)}")

    # ---- exact-coverage LP: the 254 tournaments 3-inducible but not with unit margin
    r254 = load("face254_*.jsonl", 254)
    c254, _ = classify(r254, True)
    order = sorted(c254, key=lambda k: (c254[k]["alpha"], len(c254[k]["arcs"]), -len(c254[k]["tour"]),
                                        min(c254[k]["tour"]), k))
    ids = {k: f"U{j:02d}" for j, k in enumerate(order, 1)}
    rows = []
    for k in order:
        d, rk = describe(c254[k])
        d.update(id=ids[k], converse=ids.get(rk, "-"))
        rows.append(d)
    cols = ["id", "alpha", "arcs", "verts", "negative_arcs", "max_mult", "total_mult", "sum_mult", "n_supports",
            "n_tournaments", "converse", "degseq", "arclist"]
    write("n9_signed_obstacles_254.tsv", rows, cols)
    print(f"254: {sum(len(r['supports']) for r in r254)} minimal signed supports, {len(c254)} classes; "
          f"alpha^= {sorted(Counter(r['alpha'] for r in r254).items(), key=lambda kv: Fraction(kv[0]))}")


if __name__ == "__main__":
    main()
