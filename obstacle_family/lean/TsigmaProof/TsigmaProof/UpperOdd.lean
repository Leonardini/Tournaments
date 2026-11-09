import TsigmaProof.Odd
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# The odd family: Alice's side (Proposition `prop:family-bound` of paper 1)

Alice puts weight 1 on each of the `6k + 23` arcs of `H_{2k+9}`.  Every ranking makes at most
`4k + 15 = 2n - 3` of them forward: the hub triangles, the twelve triangles of Table
`tbl:fixed-triangles` and the defect 4-cycle cover every arc exactly twice (Appendix
`sec:family-cover`).  The case `k = 0` (`n = 9`, zigzag path `P1 → H`) is treated separately.
-/

namespace Tsigma.Odd

/-- `1` if the ranking `r` makes `x → y` forward, `0` otherwise. -/
def fw (r : V → ℕ) (x y : V) : ℕ := if r x < r y then 1 else 0

theorem tri (r : V → ℕ) (x y z : V) : fw r x y + fw r y z + fw r z x ≤ 2 := by
  unfold fw; split_ifs <;> omega

theorem quad (r : V → ℕ) (w x y z : V) : fw r w x + fw r x y + fw r y z + fw r z w ≤ 3 := by
  unfold fw; split_ifs <;> omega

theorem list_range_sum (g : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map g).sum = ∑ t ∈ Finset.range m, g t := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The 22 arcs of `H_n` that do not depend on `k`: 18 among the fixed vertices away from the
zigzag path, and the four arcs between the hubs and the ends `P1`, `H` of the path. -/
def fixedArcs : List ((V × V) × ℕ) :=
  [((.N0, .N2), 1), ((.N0, .N3), 1), ((.N1, .N2), 1), ((.N1, .N3), 1), ((.N2, .N3), 1),
   ((.P1, .N0), 1), ((.N0, .P2), 1), ((.N2, .P2), 1), ((.P2, .N1), 1), ((.P2, .G), 1),
   ((.N2, .F), 1), ((.N3, .F), 1), ((.F, .N0), 1), ((.F, .N1), 1), ((.N3, .G), 1),
   ((.G, .N0), 1), ((.G, .N2), 1), ((.N3, .H), 1),
   ((.N1, .P1), 1), ((.N2, .P1), 1), ((.H, .N1), 1), ((.H, .N2), 1)]

/-- Alice's strategy for `k ≥ 1`: every arc of `H_{2k+9}`, with weight 1. -/
def oarcs (k : ℕ) : List ((V × V) × ℕ) :=
  fixedArcs ++ [((.P1, .W 1), 1), ((.U k, .H), 1)]
  ++ (List.range k).map (fun t => ((.N1, .U (t + 1)), 1))
  ++ (List.range k).map (fun t => ((.N2, .U (t + 1)), 1))
  ++ (List.range k).map (fun t => ((.W (t + 1), .N1), 1))
  ++ (List.range k).map (fun t => ((.W (t + 1), .N2), 1))
  ++ (List.range k).map (fun t => ((.U (t + 1), .W (t + 1)), 1))
  ++ (List.range (k - 1)).map (fun t => ((.U (t + 1), .W (t + 2)), 1))

/-- Alice's strategy for `k = 0`: the 23 arcs of `H_9`. -/
def oarcs0 : List ((V × V) × ℕ) := fixedArcs ++ [((.P1, .H), 1)]

theorem oarcs_total (k : ℕ) (hk : 1 ≤ k) : ((oarcs k).map Prod.snd).sum = 6 * k + 23 := by
  simp only [oarcs, fixedArcs, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    List.map_nil, List.sum_nil, List.map_map, Function.comp_def, sum_map_range_one]
  omega

theorem oarcs0_total : (oarcs0.map Prod.snd).sum = 23 := by
  simp [oarcs0, fixedArcs]

theorem oarcs_arcs (k : ℕ) (hk : 1 ≤ k) :
    ∀ q ∈ oarcs k, valid k q.1.1 ∧ valid k q.1.2 ∧ garc k q.1.1 q.1.2 := by
  intro q hq
  simp only [oarcs, fixedArcs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hq
  rcases hq with ((((((((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h) | (h | h)) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) |
    ⟨t, ht, h⟩) <;>
    (subst h; simp only [valid, garc, and_true, true_and, and_self]; try omega)

theorem oarcs0_arcs : ∀ q ∈ oarcs0, valid 0 q.1.1 ∧ valid 0 q.1.2 ∧ garc 0 q.1.1 q.1.2 := by
  intro q hq
  simp only [oarcs0, fixedArcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h) | h <;>
    (subst h; simp [valid, garc])

theorem fixed_fwd (r : V → ℕ) :
    (fixedArcs.map (fun q => if r q.1.1 < r q.1.2 then q.2 else 0)).sum =
      fw r .N0 .N2 + fw r .N0 .N3 + fw r .N1 .N2 + fw r .N1 .N3 + fw r .N2 .N3
      + fw r .P1 .N0 + fw r .N0 .P2 + fw r .N2 .P2 + fw r .P2 .N1 + fw r .P2 .G
      + fw r .N2 .F + fw r .N3 .F + fw r .F .N0 + fw r .F .N1 + fw r .N3 .G
      + fw r .G .N0 + fw r .G .N2 + fw r .N3 .H
      + fw r .N1 .P1 + fw r .N2 .P1 + fw r .H .N1 + fw r .H .N2 := by
  simp only [fixedArcs, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, fw]
  ring

/-- The twelve triangles on fixed vertices and the defect 4-cycle: with the four hub triangles of
the two ends of the path, they cover the 22 arcs of `fixedArcs` exactly twice. -/
theorem fixed_cycles (r : V → ℕ) :
    2 * (fw r .N0 .N2 + fw r .N0 .N3 + fw r .N1 .N2 + fw r .N1 .N3 + fw r .N2 .N3
      + fw r .P1 .N0 + fw r .N0 .P2 + fw r .N2 .P2 + fw r .P2 .N1 + fw r .P2 .G
      + fw r .N2 .F + fw r .N3 .F + fw r .F .N0 + fw r .F .N1 + fw r .N3 .G
      + fw r .G .N0 + fw r .G .N2 + fw r .N3 .H)
      + fw r .N1 .P1 + fw r .N2 .P1 + fw r .H .N1 + fw r .H .N2 ≤ 27 := by
  have := tri r .N2 .F .N0
  have := tri r .N2 .F .N1
  have := tri r .N3 .F .N0
  have := tri r .N3 .F .N1
  have := tri r .N3 .G .N0
  have := tri r .N3 .G .N2
  have := tri r .N0 .P2 .G
  have := tri r .N2 .P2 .G
  have := tri r .N3 .H .N1
  have := tri r .N3 .H .N2
  have := tri r .N2 .P1 .N0
  have := tri r .N2 .P2 .N1
  have := quad r .N0 .P2 .N1 .P1
  omega

/-- Alice's side for `k ≥ 1`: every ranking makes at most `4k + 15 = 2n - 3` arcs forward. -/
theorem alice (k : ℕ) (hk : 1 ≤ k) : AliceFwd (oarcs k) (4 * k + 15) := by
  intro r
  have hfx := fixed_fwd r
  have hcy := fixed_cycles r
  simp only [oarcs, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil, List.map_map, Function.comp_def, list_range_sum]
  rw [hfx]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hdiag : ∑ t ∈ Finset.range (m + 1),
      (2 * fw r (.U (t + 1)) (.W (t + 1)) + fw r .N1 (.U (t + 1)) + fw r .N2 (.U (t + 1))
        + fw r (.W (t + 1)) .N1 + fw r (.W (t + 1)) .N2) ≤ ∑ t ∈ Finset.range (m + 1), 4 := by
    apply Finset.sum_le_sum
    intro t _
    have h1 := tri r (.U (t + 1)) (.W (t + 1)) .N1
    have h2 := tri r (.U (t + 1)) (.W (t + 1)) .N2
    omega
  have hoff : ∑ t ∈ Finset.range m,
      (2 * fw r (.U (t + 1)) (.W (t + 2)) + fw r .N1 (.U (t + 1)) + fw r .N2 (.U (t + 1))
        + fw r (.W (t + 1 + 1)) .N1 + fw r (.W (t + 1 + 1)) .N2) ≤ ∑ t ∈ Finset.range m, 4 := by
    apply Finset.sum_le_sum
    intro t _
    have h1 : fw r (.U (t + 1)) (.W (t + 2)) + fw r (.W (t + 1 + 1)) .N1 + fw r .N1 (.U (t + 1)) ≤ 2 :=
      tri r (.U (t + 1)) (.W (t + 2)) .N1
    have h2 : fw r (.U (t + 1)) (.W (t + 2)) + fw r (.W (t + 1 + 1)) .N2 + fw r .N2 (.U (t + 1)) ≤ 2 :=
      tri r (.U (t + 1)) (.W (t + 2)) .N2
    omega
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hdiag hoff
  -- index shifts: the sums over W start at W_1, those over U end at U_{m+1}
  have sW1 := Finset.sum_range_succ' (fun t => fw r (.W (t + 1)) .N1) m
  have sW2 := Finset.sum_range_succ' (fun t => fw r (.W (t + 1)) .N2) m
  have sU1 := Finset.sum_range_succ (fun t => fw r .N1 (.U (t + 1))) m
  have sU2 := Finset.sum_range_succ (fun t => fw r .N2 (.U (t + 1))) m
  simp only [Nat.zero_add] at sW1 sW2
  -- the hub triangles of the two ends of the path
  have e1 := tri r .P1 (.W 1) .N1
  have e2 := tri r .P1 (.W 1) .N2
  have e3 := tri r (.U (m + 1)) .H .N1
  have e4 := tri r (.U (m + 1)) .H .N2
  simp only [fw] at hcy e1 e2 e3 e4 sW1 sW2 sU1 sU2 hdiag hoff ⊢
  omega

/-- Alice's side for `k = 0`: every ranking makes at most `15 = 2 · 9 - 3` arcs of `H_9` forward. -/
theorem alice0 : AliceFwd oarcs0 15 := by
  intro r
  have hfx := fixed_fwd r
  have hcy := fixed_cycles r
  simp only [oarcs0, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil]
  rw [hfx]
  have e1 := tri r .P1 .H .N1
  have e2 := tri r .P1 .H .N2
  simp only [fw] at hcy e1 e2 ⊢
  omega

end Tsigma.Odd
