#!/usr/bin/env python3
"""check_family_appendix.py -- checks Section sec:family and Appendix app:family of paper 1 against the
manuscript itself.  Everything is read from Tournaments_3_and_5_voters_MSS.md (tables and the two displayed
completion orders); G_n and H_n are rebuilt from the definitions of Section sec:family-def, written out again
below.  For every k in range (KMAX on the command line, default 25) it checks:
  * the double cover of Appendix sec:family-cover (tbl:fixed-triangles);
  * tbl:even-orders: total 2(3n - 4), load exactly 2(n - 1) on G_n, at most 2(n - 1) - 1 elsewhere (k >= 2);
  * tbl:even-loads: its rows partition the arcs of G^_n and every printed entry equals the recomputed
    group count (k >= 3);
  * tbl:odd-orders: each of the six sets A..F has total 3n - 4, load exactly n - 1 on H_n, at most n - 1
    elsewhere, and every arc outside H_n has load at most n - 2 in at least one set (k >= 1);
  * tbl:even-dual-orders is an optimal Bob strategy for G_n and every move of tbl:even-moves (and its image
    under phi = (T1 T2)(P1 P2)) changes exactly the two stated arcs of G_n; the orders h, Q_3 of step (v);
  * every relation of tbl:odd-relations (k >= 1; a family index k is the last member) changes exactly the two
    stated arcs, passing fixed vertices only, and the relations form a strongly connected digraph on the 22
    fixed arcs; the hub chains, ends and the heavy order A_1 of Appendix sec:family-dual-odd;
  * tbl:small-orders-8 / -9: strict certificates X_8, X_9 and optimal strategies Y_8, Y_9, rank 20 and 23;
  * the example of Section sec:family-tournaments (G_10 along T0..W2 contains G_8).
FAMILY_MD points it at another copy of the manuscript (negative controls).  Any failure is an AssertionError
naming the table, row and k.
Usage: check_family_appendix.py [KMAX=25]
"""
import re, sys
from fractions import Fraction
from itertools import permutations
from pathlib import Path

import os
# FAMILY_MD points the checker at another copy of the manuscript (used for the negative controls)
MD = Path(os.environ.get("FAMILY_MD", Path(__file__).resolve().parent / "Tournaments_3_and_5_voters_MSS.md"))
TEXT = MD.read_text()
KMAX = 30           # set from the command line in main()


# ---------------------------------------------------------------- the two families (Section sec:family-def)
def family_G(k):
    """G_{2k+6}: hubs T1, T2; zigzag path T0 U1 W1 ... Uk Wk T3."""
    assert k >= 1
    V = ["T0", "T1", "T2", "T3", "P1", "P2"] + [f"U{i}" for i in range(1, k + 1)] + [f"W{i}" for i in range(1, k + 1)]
    path = ["T0"] + [x for i in range(1, k + 1) for x in (f"U{i}", f"W{i}")] + ["T3"]
    Uv = [f"U{i}" for i in range(1, k + 1)] + ["T3"]
    Wv = ["T0"] + [f"W{i}" for i in range(1, k + 1)]
    E = set()
    for a, b in zip(path, path[1:]):             # path arcs go from the U-vertex to the W-vertex
        E.add((a, b) if a in Uv else (b, a))
    for h in ("T1", "T2"):
        E |= {(h, u) for u in Uv} | {(w, h) for w in Wv}
    E |= {("T0", "T3"), ("T2", "P1"), ("T3", "P1"), ("P1", "T0"), ("P1", "T1"),
          ("T1", "P2"), ("T3", "P2"), ("P2", "T0"), ("P2", "T2")}
    n = 2 * k + 6
    assert len(V) == n and len(E) == 3 * n - 4, (k, len(E))
    defect = [("T1", "P2"), ("P2", "T2"), ("T2", "P1"), ("P1", "T1")]
    return V, E, path, Uv, Wv, ("T1", "T2"), defect


def family_H(k):
    """H_{2k+9}: hubs N1, N2; zigzag path P1 W1 U1 W2 ... Wk Uk H."""
    assert k >= 0
    V = ["N0", "N1", "N2", "N3", "P1", "P2", "F", "G", "H"] + [f"U{i}" for i in range(1, k + 1)] + [f"W{i}" for i in range(1, k + 1)]
    path = ["P1"] + [x for i in range(1, k + 1) for x in (f"W{i}", f"U{i}")] + ["H"]
    Uv = ["P1"] + [f"U{i}" for i in range(1, k + 1)]
    Wv = [f"W{i}" for i in range(1, k + 1)] + ["H"]
    E = set()
    for a, b in zip(path, path[1:]):
        E.add((a, b) if a in Uv else (b, a))
    for h in ("N1", "N2"):
        E |= {(h, u) for u in Uv} | {(w, h) for w in Wv}
    E |= {(a, b) for a in ("N0", "N1") for b in ("N2", "N3")}
    E |= {("N2", "N3"), ("P1", "N0"), ("N0", "P2"), ("N2", "P2"), ("P2", "N1"), ("P2", "G"),
          ("N2", "F"), ("N3", "F"), ("F", "N0"), ("F", "N1"), ("N3", "G"), ("G", "N0"), ("G", "N2"), ("N3", "H")}
    n = 2 * k + 9
    assert len(V) == n and len(E) == 3 * n - 4, (k, len(E))
    defect = [("N0", "P2"), ("P2", "N1"), ("N1", "P1"), ("P1", "N0")]
    return V, E, path, Uv, Wv, ("N1", "N2"), defect


# ---------------------------------------------------------------- reading the manuscript
def table(label):
    """rows (lists of cell strings) of the pipe table whose caption carries {#label ...}"""
    m = re.search(r"\{#" + re.escape(label) + r"[ }]", TEXT)
    assert m, f"no table {label} in the manuscript"
    lines = TEXT[:m.start()].split("\n")
    i = len(lines) - 1
    while not lines[i].startswith("|"):         # skip the caption line(s) back to the table
        i -= 1
    rows = []
    while i >= 0 and lines[i].startswith("|"):
        rows.append([c.strip() for c in lines[i].strip().strip("|").split("|")])
        i -= 1
    rows.reverse()
    assert re.fullmatch(r"[-:| ]+", "|".join(rows[1])), f"{label}: no header separator"
    return rows[0], rows[2:]


def vname(tok):
    """'T_0' -> 'T0', 'W_k' with k -> 'W5' handled by caller; F, G, H unchanged"""
    tok = tok.strip()
    m = re.fullmatch(r"([A-Z])_\{?(\d+)\}?", tok)
    if m:
        return m.group(1) + m.group(2)
    assert re.fullmatch(r"[FGH]", tok), f"unknown vertex token {tok!r}"
    return tok


def evalk(expr, **var):
    """evaluate a cell like '$2k+5$', '$k-i+1$', '3' at integer values"""
    e = expr.replace("$", "").replace(" ", "")
    if e == "":
        return None
    e = re.sub(r"(\d)([a-z])", r"\1*\2", e)
    assert re.fullmatch(r"[0-9a-z+\-*]+", e), f"cannot evaluate {expr!r}"
    return eval(e, {"__builtins__": {}}, dict(var))


# ---------------------------------------------------------------- orders and loads
def check_order(order, V, where):
    assert sorted(order) == sorted(V), f"{where}: not a linear order of the vertices: {order}"


def loads(cert, arcs):
    pos = [({x: p for p, x in enumerate(o)}, w) for w, o, _ in cert]
    return {a: sum(w for ps, w in pos if ps[a[1]] < ps[a[0]]) for a in arcs}


def completion(V, E, lam):
    rank = {x: p for p, x in enumerate(lam)}
    assert sorted(lam) == sorted(V)
    T = set(E)
    for x in V:
        for y in V:
            if x < y and (x, y) not in E and (y, x) not in E:
                T.add((x, y) if rank[x] < rank[y] else (y, x))
    assert len(T) == len(V) * (len(V) - 1) // 2
    return T


def reference_orders():
    """the two displayed orders of Section sec:family-tournaments, as token lists with k symbolic"""
    sec = TEXT[TEXT.index("### Tournaments that attain the bound"):TEXT.index("**Theorem []{#thm:family-value}")]
    disp = re.findall(r"\$\$(.*?)\$\$", sec, re.S)
    assert len(disp) == 2, disp
    return [[t.strip() for t in d.replace("\\ ", " ").rstrip(",. ").split(",")] for d in disp]


def expand_ref(tokens, k):
    out = []
    for t in tokens:
        if t == "\\dots":
            continue
        out.append(t)
    # "W_1, \dots, W_k" -> W1..Wk ; "U_2, \dots, U_k" -> U2..Uk
    res, i = [], 0
    while i < len(out):
        t = out[i]
        if i + 1 < len(out) and re.fullmatch(r"[UW]_\d", t) and re.fullmatch(r"[UW]_k", out[i + 1]) and t[0] == out[i + 1][0]:
            res += [f"{t[0]}{j}" for j in range(int(t[2:]), k + 1)]; i += 2
        else:
            res.append(vname(t)); i += 1
    return res


STATS = {"moves": 0, "relations": 0, "load-table arcs": 0, "even orders": 0, "odd orders": 0}


# ---------------------------------------------------------------- reading the order tables
def ladder(k):
    U = {i: f"U{i}" for i in range(1, k + 1)}; W = {i: f"W{i}" for i in range(1, k + 1)}
    return U, W


def idx_value(e, k, var=None):
    """an index written in the paper ('1', 'k', 'k-1', 'i+1', 's-1', ...) at integers"""
    e = e.replace(" ", "")
    env = {"k": k}; env.update(var or {})
    assert re.fullmatch(r"[0-9a-z+\-]+", e), f"index {e!r}"
    return eval(re.sub(r"(\d)([a-z])", r"\1*\2", e), {"__builtins__": {}}, env)


def even_sequences(k):
    S = [(f"U{i}", f"W{i}") for i in range(k, 0, -1)]
    M = [(f"U{i + 1}", f"W{i}") for i in range(1, k)]
    return S, M


def flat(pairs):
    return [x for p in pairs for x in p]


def expand_even(cell, k, var):
    """an order cell of tbl:even-orders / tbl:even-dual-orders at k, with the family index in var"""
    S, M = even_sequences(k)
    Sp = flat(S)[:-1]                          # S' = S without its last vertex W1
    out = []
    for tok in cell.replace("$", "").split("\\ "):
        t = tok.strip()
        if not t:
            continue
        m = re.fullmatch(r"([UW])_\{(.+):(.+)\}", t)
        if m:
            a, b = idx_value(m.group(2), k, var), idx_value(m.group(3), k, var)
            out += [f"{m.group(1)}{i}" for i in range(a, b + 1)]; continue
        m = re.fullmatch(r"(S|S'|M)_\{(\\le|>)\s*([a-z0-9+\- ]+)\}", t)
        if m:
            j = idx_value(m.group(3), k, var)
            seq = {"S": flat(S), "S'": Sp, "M": flat(M)}[m.group(1)]
            out += seq[:2 * j] if m.group(2) == "\\le" else seq[2 * j:]; continue
        if t == "S": out += flat(S); continue
        if t == "S_2": out += flat(S[:-1]); continue
        if t == "M": out += flat(M); continue
        m = re.fullmatch(r"\\tilde\s*(S|M)_([a-z])", t)
        if m:
            s = var[m.group(2)]
            if m.group(1) == "S":
                seq = [x for (u, w) in S for x in ((w, "T1", u) if u == f"U{s}" else (u, w))]
            else:
                seq = [x for (u, w) in M for x in ((w, "T1", u) if (u, w) == (f"U{s + 1}", f"W{s}") else (u, w))]
            out += seq; continue
        m = re.fullmatch(r"([UW])_\{?([0-9k][0-9k+\-]*)\}?", t)
        if m and m.group(1) in "UW":
            out.append(f"{m.group(1)}{idx_value(m.group(2), k, var)}"); continue
        out.append(vname(t))
    return out


def odd_sequences(k):
    E = [(f"U{i}", f"W{i}") for i in range(1, k + 1)]
    D = [(f"U{i}", f"W{i + 1}") for i in range(k - 1, 0, -1)]
    return E, D


def expand_odd(cell, k, var):
    E, D = odd_sequences(k)
    out = []
    for tok in cell.replace("$", "").split("\\ "):
        t = tok.strip()
        if not t:
            continue
        m = re.fullmatch(r"([UW])_\{1:k\}", t)
        if m:
            out += [f"{m.group(1)}{i}" for i in range(1, k + 1)]; continue
        m = re.fullmatch(r"(E|D)_\{(\\le|>)\s*j\}", t)
        if m:
            seq = flat(E if m.group(1) == "E" else D); j = var["j"]
            out += seq[:2 * j] if m.group(2) == "\\le" else seq[2 * j:]; continue
        if t == "E": out += flat(E); continue
        if t == "D": out += flat(D); continue
        if t == "U_k": out.append(f"U{k}"); continue
        if t == "W_1": out.append("W1"); continue
        out.append(vname(t))
    return out


def weight_of(cell, k):
    c = cell.replace("$", "").replace("each", "").strip()
    return idx_value(c, k)


def family_range(name, k):
    """'$A_j$, $0 \\le j \\le k$' -> ('j', range)"""
    m = re.search(r"\$(\d+) \\le ([a-z]) \\le (k(?: ?- ?1)?)\$", name)
    if not m:
        return None, None
    hi = k if m.group(3) == "k" else k - 1
    return m.group(2), range(int(m.group(1)), hi + 1)


def read_orders(label, k, expand):
    """[(row name, member index or None, weight, order)] for every order of the table at k"""
    hdr, rows = table(label)
    out = []
    for row in rows:
        name, cell, w = row[0], row[1], row[2]
        v, rng = family_range(name, k)
        if v is None:
            out.append((name.split(",")[0].replace("$", "").strip(), None, weight_of(w, k), expand(cell, k, {})))
        else:
            for x in rng:
                out.append((name.split(",")[0].replace("$", "").strip(), x, weight_of(w, k), expand(cell, k, {v: x})))
    return out


def fwd(order, a):
    return order.index(a[0]) < order.index(a[1])


def load_map(cert, arcs):
    pos = [({x: p for p, x in enumerate(o)}, w) for _, _, w, o in cert]
    return {a: sum(w for ps, w in pos if ps[a[1]] < ps[a[0]]) for a in arcs}


def completion_of(fam, k, ref):
    V, E, path, Uv, Wv, hubs, defect = (family_G if fam == "even" else family_H)(k)
    return V, E, completion(V, E, expand_ref(ref, k)), path, Uv, hubs, defect


# ---------------------------------------------------------------- the even load table
VT = r"([A-Z])_\{?([0-9a-z+\-]+)\}?|([FGH])"


def parse_label(cell):
    """[(x-term, y-term, [conditions])] from a cell like '$U_{i} \\to U_{j}$, $j \\ge i+3$, $P_1 \\to T_0$'"""
    items = re.findall(r"\$([^$]*)\$", cell)
    pats = []
    for it in items:
        if "\\to" in it:
            x, y = [s.strip() for s in it.split("\\to")]
            pats.append([x, y, []])
        else:
            pats[-1][2].append(it.strip())
    return pats


def term_vertex(t, k, var):
    m = re.fullmatch(r"([A-Z])_\{?([0-9a-z+\-]+)\}?", t)
    if not m:
        return vname(t), False
    if m.group(1) in "UW":
        e = m.group(2)
        # an index written other than 1 or k (i, j, 2, 3, k-1, i+1, ...) is an interior one, 2..k-1
        return f"{m.group(1)}{idx_value(e, k, var)}", e not in ("1", "k")
    return vname(t), False


def pattern_arcs(p, k):
    x, y, conds = p
    vars_ = sorted(set(re.findall(r"(?<![a-z])([ij])(?![a-z])", x + y + " ".join(conds))))
    out = []
    import itertools
    for vals in itertools.product(range(2, k), repeat=len(vars_)):
        var = dict(zip(vars_, vals))
        ok = True
        for c in conds:
            e = c.replace("\\ge", ">=").replace("\\le", "<=").replace(" ", "")
            e = re.sub(r"(\d)([a-z])", r"\1*\2", e)
            if not eval(e, {"__builtins__": {}}, dict(var, k=k)): ok = False
        if not ok:
            continue
        vx, gx = term_vertex(x, k, var); vy, gy = term_vertex(y, k, var)
        ix = lambda v: int(v[1:]) if v[0] in "UW" and v[1:].isdigit() else None
        if gx and not (2 <= ix(vx) <= k - 1): continue
        if gy and not (2 <= ix(vy) <= k - 1): continue
        if ix(vx) is not None and not (1 <= ix(vx) <= k): continue
        if ix(vy) is not None and not (1 <= ix(vy) <= k): continue
        out.append(((vx, vy), var))
    return out


def check_even_load_table(k, T, E, cert):
    hdr, rows = table("tbl:even-loads")
    cols = {"R": lambda nm: nm.startswith("R_"), "A": lambda nm: nm.startswith("A"),
            "B": lambda nm: nm.startswith("B"), "C": lambda nm: nm.startswith("C")}
    groups = {}
    for nm, _, w, o in cert:
        g = [c for c, f in cols.items() if f(nm)]
        assert len(g) == 1, nm
        groups.setdefault(g[0], []).append((nm, None, w, o))
    gl = {g: load_map(c, T) for g, c in groups.items()}
    seen = {}
    n = 2 * k + 6
    for row in rows:
        for p in parse_label(row[0]):
            for a, var in pattern_arcs(p, k):
                assert a in T, f"tbl:even-loads k={k}: row {row[0]!r} names {a}, not an arc of the completion"
                assert a not in seen, f"tbl:even-loads k={k}: arc {a} in rows {seen[a]!r} and {row[0]!r}"
                seen[a] = row[0]; STATS["load-table arcs"] += 1
                ia = int(a[0][1:]) if a[0][0] in "UW" else None
                ib = int(a[1][1:]) if a[1][0] in "UW" else None
                vv = {}
                if ia is not None and ib is not None: vv = {"i": ia, "j": ib}
                elif ia is not None or ib is not None: vv = {"i": ia if ia is not None else ib}
                if "i" in vv and "j" not in vv: vv["j"] = vv["i"]
                if "i" not in vv: vv = {"i": 0, "j": 0}
                for c, g in zip(row[1:5], ("R", "A", "B", "C")):
                    assert evalk(c, k=k, **vv) == gl[g][a], f"tbl:even-loads k={k} row {row[0]!r} column {g} arc {a}: printed {c} = {evalk(c, k=k, **vv)}, recomputed {gl[g][a]}"
                tot = evalk(row[5], k=k, **vv)
                assert tot == sum(gl[g][a] for g in gl), f"tbl:even-loads k={k} row {row[0]!r}: load"
                assert (tot == 2 * (n - 1)) == (a in E), f"tbl:even-loads k={k}: load {tot} on {a} (member {a in E})"
    missing = set(T) - set(seen)
    assert not missing, f"tbl:even-loads k={k}: arcs in no row: {sorted(missing)[:6]}"


# ---------------------------------------------------------------- moves
PHI = {"T1": "T2", "T2": "T1", "P1": "P2", "P2": "P1"}


def move(order, v, target, where):
    """move v to just before (where = 'before') or just after target; returns new order and passed vertices"""
    o = [x for x in order if x != v]
    t = o.index(target)
    o.insert(t if where == "before" else t + 1, v)
    a, b = sorted((order.index(v), o.index(v)))
    passed = [x for x in (order if order.index(v) < o.index(v) else o)[a:b + 1] if x != v]
    lo, hi = sorted((order.index(v), o.index(v)))
    old_between = order[lo:hi + 1] if order.index(v) < o.index(v) else order[lo:hi + 1]
    return o, set(order[min(order.index(v), o.index(v)):max(order.index(v), o.index(v)) + 1]) - {v}


def check_move(order, v, target, where, g, l, E, ctx):
    """moving v changes exactly the arcs g (to forward) and l (to backward) of E"""
    assert v in order and target in order, ctx
    new, passed = move(order, v, target, where)
    changed = [a for a in E if fwd(order, a) != fwd(new, a)]
    assert sorted(changed) == sorted([g, l]), f"{ctx}: arcs changed {changed}, stated gain {g}, loss {l}"
    assert fwd(new, g) and not fwd(order, g) and fwd(order, l) and not fwd(new, l), f"{ctx}: wrong directions"


def arcs_in(text, k, var):
    """'y(W_iT_1) \\le y(U_iW_i)' -> two arcs"""
    out = []
    for inner in re.findall(r"y\(([^)]*)\)", text):
        toks = re.findall(r"[A-Z]_\{[^}]*\}|[A-Z]_[0-9a-z]|[FGH](?!_)", inner.replace("\\to", "").replace(" ", ""))
        assert len(toks) == 2, (text, toks)
        out.append(tuple(term_vertex(t, k, var)[0] for t in toks))
    return out


def check_even_moves(k, E):
    dual = read_orders("tbl:even-dual-orders", k, expand_even)
    names = {}
    for nm, x, w, o in dual:
        names[(nm, x)] = o
    hdr, rows = table("tbl:even-moves")
    for row in rows:
        tag = row[0].strip()
        irange = range(1, k + 1) if tag in ("H1", "H2", "H3") else range(1, k) if tag in ("H4", "H5", "H6") else [None]
        oname = row[1].split(":")[0].replace("$", "").strip()
        mv = re.fullmatch(r"\$(.+?)\$ (before|after) \$(.+?)\$", row[2].strip())
        assert mv, row[2]
        for i in irange:
            var = {} if i is None else {"i": i}
            phi = oname.startswith("\\varphi")
            base = oname.replace("\\varphi", "").strip()
            m = re.fullmatch(r"(\\tilde\s*)?([A-Za-z])(?:_\{?([^{}]*)\}?)?", base)
            assert m, base
            letter = (m.group(1) or "").replace(" ", "") + m.group(2)
            sub = m.group(3)
            key = None
            for (nm, x) in names:
                nmn = nm.replace(" ", "")
                if x is None and sub is not None and nmn in (f"{letter}_{{{sub}}}", f"{letter}_{sub}"):
                    key = (nm, None)
                elif x is None and sub is None and nmn == letter:
                    key = (nm, None)
                elif x is not None and sub is not None and re.fullmatch(re.escape(letter) + r"_[a-z]", nmn) and x == idx_value(sub, k, var):
                    key = (nm, x)
            assert key is not None, f"tbl:even-moves {tag} k={k} i={i}: no order named {oname}"
            o = names[key]
            if phi:
                o = [PHI.get(x, x) for x in o]
            v = term_vertex(mv.group(1), k, var)[0]; tg = term_vertex(mv.group(3), k, var)[0]
            g, l = arcs_in(row[3], k, var)
            check_move(o, v, tg, mv.group(2), g, l, E, f"tbl:even-moves {tag} k={k} i={i}")
            STATS["moves"] += 1
            # the image under phi
            check_move([PHI.get(x, x) for x in o], PHI.get(v, v), PHI.get(tg, tg), mv.group(2),
                       tuple(PHI.get(x, x) for x in g), tuple(PHI.get(x, x) for x in l), E,
                       f"tbl:even-moves {tag} (phi image) k={k} i={i}")
    # step (v): U1 -> T0 backward in h, forward in Q_3, both of positive weight
    h = [o for (nm, x), o in names.items() if nm == "h"][0]
    q3 = [o for (nm, x), o in names.items() if nm.replace("{", "").replace("}", "") == "Q_3"][0]
    assert not fwd(h, ("U1", "T0")) and fwd(q3, ("U1", "T0")), "step (v): h and Q_3"


# ---------------------------------------------------------------- odd: relations, hub chains, ends
def odd_order_index(cert):
    idx = {}
    for nm, x, w, o in cert:
        idx[(nm.replace(" ", ""), x)] = o
    return idx


def odd_lookup(idx, name, j=None):
    key = (name.replace(" ", ""), j)
    return idx.get(key)


def check_odd_relations(k, E, cert):
    import networkx as nx
    idx = odd_order_index(cert)
    hdr, rows = table("tbl:odd-relations")
    fixed = {"N0", "N1", "N2", "N3", "P1", "P2", "F", "G", "H"}
    G = nx.DiGraph()
    used = 0
    for row in rows:
        b_, a_ = arcs_in(row[0].replace("\\ge", "|"), k, {})[1], arcs_in(row[0], k, {})[0]
        a, b = arcs_in(row[0], k, {})          # y(a) >= y(b): b gains, a is lost
        m = re.fullmatch(r"\$([A-F])(?:_\{(\d+)\}|\^\{([ED]\d)\}_\{(\d+|k)\})\$", row[1].strip())
        assert m, row[1]
        if m.group(2):
            o = odd_lookup(idx, f"{m.group(1)}_{{{m.group(2)}}}")
        else:
            j = k if m.group(4) == "k" else int(m.group(4))
            o = odd_lookup(idx, f"{m.group(1)}^{{{m.group(3)}}}_j", j)
        assert o is not None, (row[1], k)
        mv = re.fullmatch(r"\$(.+?)\$ (before|after) \$(.+?)\$", row[2].strip())
        v, tg = vname(mv.group(1)), vname(mv.group(3))
        check_move(o, v, tg, mv.group(2), b, a, E, f"tbl:odd-relations k={k} {row[0]}")
        new, passed = move(o, v, tg, mv.group(2))
        assert passed <= fixed, f"tbl:odd-relations k={k} {row[0]}: the move passes ladder vertices {passed - fixed}"
        G.add_edge(b, a); used += 1; STATS["relations"] += 1
    fixed_arcs = [a for a in E if a[0] in fixed and a[1] in fixed]
    assert len(fixed_arcs) == 22 and set(G.nodes) == set(fixed_arcs) and nx.is_strongly_connected(G), \
        f"tbl:odd-relations k={k}: the relations do not join the 22 fixed arcs strongly ({used} used)"
    return used


def check_odd_chains(k, E, cert, path):
    idx = odd_order_index(cert)
    consec = lambda o, seq: any(o[p:p + len(seq)] == seq for p in range(len(o)))
    for fam, h in (("A^{E1}", "N2"), ("A^{E2}", "N1")):
        for i in range(1, k + 1):
            o1, o2 = odd_lookup(idx, fam + "_j", i - 1), odd_lookup(idx, fam + "_j", i)
            assert consec(o1, [h, f"U{i}", f"W{i}"]) and consec(o2, [f"U{i}", f"W{i}", h]), (fam, k, i)
            check_move(o1, h, f"W{i}", "after", (f"W{i}", h), (h, f"U{i}"), E, f"chain {fam} k={k} i={i} a")
            check_move(o2, h, f"U{i}", "before", (h, f"U{i}"), (f"W{i}", h), E, f"chain {fam} k={k} i={i} b")
            check_move(o2, f"U{i}", h, "after", (h, f"U{i}"), (f"U{i}", f"W{i}"), E, f"chain {fam} k={k} i={i} c")
    for fam, h in (("A^{D1}", "N2"), ("A^{D2}", "N1")):
        for i in range(1, k):
            o1, o2 = odd_lookup(idx, fam + "_j", k - 1 - i), odd_lookup(idx, fam + "_j", k - i)
            assert consec(o1, [h, f"U{i}", f"W{i + 1}"]) and consec(o2, [f"U{i}", f"W{i + 1}", h]), (fam, k, i)
            check_move(o1, h, f"W{i + 1}", "after", (f"W{i + 1}", h), (h, f"U{i}"), E, f"chain {fam} k={k} i={i} a")
            check_move(o2, h, f"U{i}", "before", (h, f"U{i}"), (f"W{i + 1}", h), E, f"chain {fam} k={k} i={i} b")
            check_move(o2, f"U{i}", h, "after", (h, f"U{i}"), (f"U{i}", f"W{i + 1}"), E, f"chain {fam} k={k} i={i} c")
    # ends
    last1, last2 = odd_lookup(idx, "A^{D1}_j", k - 1), odd_lookup(idx, "A^{D2}_j", k - 1)
    f17, a19, first2 = odd_lookup(idx, "F_{17}"), odd_lookup(idx, "A_{19}"), odd_lookup(idx, "A^{D2}_j", 0)
    assert consec(last1, ["N2", "P1", "W1"]) and consec(f17, ["P1", "W1", "N2"]), "ends N2"
    assert consec(last2, ["N1", "P1", "W1"]) and consec(a19, ["P1", "W1", "N1"]), "ends N1"
    assert consec(first2, [f"U{k}", "H", "N1"]), "ends U_k H N1"
    check_move(last1, "N2", "W1", "after", ("W1", "N2"), ("N2", "P1"), E, "end N2 a")
    check_move(f17, "N2", "P1", "before", ("N2", "P1"), ("W1", "N2"), E, "end N2 b")
    check_move(last2, "N1", "W1", "after", ("W1", "N1"), ("N1", "P1"), E, "end N1 a")
    check_move(a19, "N1", "P1", "before", ("N1", "P1"), ("W1", "N1"), E, "end N1 b")
    check_move(last2, "W1", "N1", "before", ("W1", "N1"), ("P1", "W1"), E, "end P1W1")
    check_move(first2, f"U{k}", "N1", "after", ("N1", f"U{k}"), (f"U{k}", "H"), E, "end UkH")
    # the heavy order A_1: positive weight, 2n - 3 arcs of H_n forward, none on the zigzag path
    a1 = [(w, o) for nm, x, w, o in cert if nm.replace(" ", "") == "A_{1}"][0]
    n = 2 * k + 9
    path_arcs = {(a, b) if (a, b) in E else (b, a) for a, b in zip(path, path[1:])}
    assert a1[0] > 0 and sum(fwd(a1[1], a) for a in E) == 2 * n - 3 and not any(fwd(a1[1], a) for a in path_arcs), "A_1"


# ---------------------------------------------------------------- n = 8 and n = 9
def small_lists(label):
    hdr, rows = table(label)
    X, Y = [], []
    for row in rows:
        for col, L in ((0, X), (2, Y)):
            if row[col].strip():
                L.append((int(row[col]), [vname(t) for t in row[col + 1].replace("$", "").split("\\,")]))
    return X, Y


def check_small(fam, ref):
    import sympy
    k = 1 if fam == "even" else 0
    V, E, T, *_ = completion_of(fam, k, ref)
    n = len(V)
    X, Y = small_lists("tbl:small-orders-8" if fam == "even" else "tbl:small-orders-9")
    for w, o in X + Y:
        check_order(o, V, f"small {fam}")
    assert sum(w for w, _ in X) == 3 * n - 4 == sum(w for w, _ in Y)
    for a in T:
        lx = sum(w for w, o in X if not fwd(o, a))
        assert (lx == n - 1) if a in E else (lx <= n - 2), (fam, "X", a, lx)
    for a in E:
        assert sum(w for w, o in Y if not fwd(o, a)) == n - 1, (fam, "Y", a)
    arcs = sorted(E)
    rank = sympy.Matrix([[1 if fwd(o, a) else 0 for a in arcs] for _, o in X + Y] + [[1] * len(arcs)]).rank()
    assert rank == len(arcs), (fam, "rank", rank)


# ---------------------------------------------------------------- main
def main():
    global KMAX
    KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 25
    ref_even, ref_odd = reference_orders()
    tri_hdr, tri_rows = table("tbl:fixed-triangles")
    fixed_tris = {"G_n": [], "H_n": []}
    cur = None
    for row in tri_rows:
        if row[0]:
            cur = row[0].replace("$", "")
        for t in row[1].split(","):
            fixed_tris[cur].append(re.findall(r"[A-Z]_\d|[FGH]", t.replace("$", "")))
    assert len(fixed_tris["G_n"]) == 6 and len(fixed_tris["H_n"]) == 12

    for fam, ks, ref in (("even", range(1, KMAX + 1), ref_even), ("odd", range(0, KMAX + 1), ref_odd)):
        for k in ks:
            V, E, T, path, Uv, hubs, defect = completion_of(fam, k, ref)
            n = len(V)
            # the double cover (Appendix sec:family-cover)
            assert all(a in E for a in defect)
            cycles = [[u, w, h] for (u, w) in [(a, b) if a in Uv else (b, a) for a, b in zip(path, path[1:])] for h in hubs]
            cycles += [[vname(x) for x in t] for t in fixed_tris["G_n" if fam == "even" else "H_n"]]
            cyc_arcs = [[(c[q], c[(q + 1) % len(c)]) for q in range(len(c))] for c in cycles] + [defect]
            assert len(cyc_arcs) == 2 * n - 3 and all(a in E for ca in cyc_arcs for a in ca), (fam, k)
            cover = {a: 0 for a in E}
            for ca in cyc_arcs:
                for a in ca:
                    cover[a] += 1
            assert set(cover.values()) == {2}, (fam, k)
            if (fam, k) in (("even", 1), ("odd", 0)):
                check_small(fam, ref)
                continue
            if fam == "even":
                cert = read_orders("tbl:even-orders", k, expand_even); STATS["even orders"] += len(cert)
                for nm, x, w, o in cert:
                    check_order(o, V, f"tbl:even-orders k={k} {nm} {x}")
                assert sum(w for *_, w, _ in cert) == 2 * (3 * n - 4), (k, sum(w for *_, w, _ in cert))
                ld = load_map(cert, T)
                for a in T:
                    assert (ld[a] == 2 * (n - 1)) if a in E else (ld[a] <= 2 * (n - 1) - 1), f"tbl:even-orders k={k}: load {ld[a]} on {a}"
                if k >= 3:
                    check_even_load_table(k, T, E, cert)
                dual = read_orders("tbl:even-dual-orders", k, expand_even)
                for nm, x, w, o in dual:
                    check_order(o, V, f"tbl:even-dual-orders k={k} {nm}")
                assert sum(w for *_, w, _ in dual) == 3 * n - 4
                ldd = load_map(dual, E)
                assert all(ldd[a] == n - 1 for a in E), f"tbl:even-dual-orders k={k}: not an optimal Bob strategy for G_n"
                check_even_moves(k, E)
            else:
                cert = read_orders("tbl:odd-orders", k, expand_odd); STATS["odd orders"] += len(cert)
                sets = {}
                for nm, x, w, o in cert:
                    check_order(o, V, f"tbl:odd-orders k={k} {nm} {x}")
                    sets.setdefault(nm.replace("$", "")[0], []).append((nm, x, w, o))
                assert sorted(sets) == list("ABCDEF")
                slack = {a: False for a in T if a not in E}
                for L, c in sets.items():
                    assert sum(w for *_, w, _ in c) == 3 * n - 4, (k, L)
                    ld = load_map(c, T)
                    for a in T:
                        assert (ld[a] == n - 1) if a in E else (ld[a] <= n - 1), f"tbl:odd-orders k={k} set {L}: load {ld[a]} on {a}"
                        if a not in E and ld[a] <= n - 2:
                            slack[a] = True
                assert all(slack.values()), f"tbl:odd-orders k={k}: no set relieves {[a for a, s in slack.items() if not s][:5]}"
                check_odd_relations(k, E, cert)
                check_odd_chains(k, E, cert, path)
        print(f"{fam} family: all checks pass for k = {ks.start}..{ks.stop - 1}", flush=True)

    # the example of Section sec:family-tournaments: G_10 along T0 T1 T2 T3 P1 P2 U1 U2 W1 W2 contains G_8
    V, E, *_ = family_G(2)
    T = completion(V, E, ["T0", "T1", "T2", "T3", "P1", "P2", "U1", "U2", "W1", "W2"])
    V8, E8, *_ = family_G(1)
    assert E8 <= T, sorted(E8 - T)
    print("G_10 completed along T0..W2 contains G_8 (identity embedding)")
    print("checked:", ", ".join(f"{v} {k}" for k, v in STATS.items()))
    print("ALL CHECKS PASS")


if __name__ == "__main__":
    main()
