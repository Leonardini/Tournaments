#!/usr/bin/env python3
"""D_11, the number of tournaments on 11 vertices, from the strong ones.

A tournament splits uniquely into an ordered sequence of strong components, each joined to every
later one by arcs pointing forward, so  D_n = sum_{k=1..n} s_k D_{n-k}  with D_0 = 1, where s_k is
the number of strong tournaments on k vertices (up to isomorphism). s_1..s_10 come from nauty's
gentourng -c -u, s_11 from the TOTAL line of n11_sweep.log (sweep_n11_strong.sh). As a check, the
recurrence must reproduce gentourng -u's D_8, D_9 and D_10.
Usage: GENTOURNG=/path/to/gentourng python3 count_tournaments_n11.py      (a minute or so)
"""
import os
import re
import subprocess

G = os.environ["GENTOURNG"]
HERE = os.path.dirname(os.path.abspath(__file__))


def count(*args):
    err = subprocess.run([G, *args], capture_output=True, text=True, check=True).stderr
    m = re.search(r">Z (\d+) graphs generated", err)
    assert m, f"gentourng {' '.join(args)}: no count line"
    return int(m.group(1))


# k = 2: a tournament on two vertices is a single arc, never strongly connected (and gentourng
# -c crashes on that empty case), so s_2 = 0 by definition rather than by count
s = {k: 0 if k == 2 else count("-c", "-u", str(k)) for k in range(1, 11)}
total = [l for l in open(os.path.join(HERE, "n11_sweep.log")) if l.startswith("n=11 strong TOTAL:")]
assert len(total) == 1, "n11_sweep.log must end with one TOTAL line"
s[11] = int(total[0].split()[3])
D = {0: 1}
for n in range(1, 12):
    D[n] = sum(s[k] * D[n - k] for k in range(1, n + 1))
for n in (8, 9, 10):
    assert D[n] == count("-u", str(n)), f"recurrence disagrees with gentourng at n = {n}"
print(f"strong tournaments on 11 vertices: {s[11]:,}")
print(f"D_11 = {D[11]:,} tournaments on 11 vertices (recurrence checked against D_8, D_9, D_10)")
