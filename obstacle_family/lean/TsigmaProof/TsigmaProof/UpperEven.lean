import TsigmaProof.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs

/-!
# The even family: Alice's side (Proposition `prop:family-bound` of paper 1)

Alice puts weight 1 on each of the `6k + 14` arcs of `G_{2k+6}`.  Every ranking makes at most
`4k + 9 = 2n - 3` of them forward: the hub triangles, the six triangles of Table
`tbl:fixed-triangles` and the defect 4-cycle cover every arc exactly twice, a triangle has at most
two forward arcs and the 4-cycle at most three (Appendix `sec:family-cover`).  Here the double
cover appears as a sum of triangle inequalities over the rungs, with two index shifts.
-/

namespace Tsigma.Even

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

/-- Alice's strategy: every arc of `G_{2k+6}`, with weight 1. -/
def oarcs (k : ℕ) : List ((V × V) × ℕ) :=
  [((.T0, .T3), 1), ((.T2, .P1), 1), ((.T3, .P1), 1), ((.P1, .T0), 1), ((.P1, .T1), 1),
   ((.T1, .P2), 1), ((.T3, .P2), 1), ((.P2, .T0), 1), ((.P2, .T2), 1),
   ((.T0, .T1), 1), ((.T0, .T2), 1), ((.T1, .T3), 1), ((.T2, .T3), 1),
   ((.U 1, .T0), 1), ((.T3, .W k), 1)]
  ++ (List.range k).map (fun t => ((.T1, .U (t + 1)), 1))
  ++ (List.range k).map (fun t => ((.T2, .U (t + 1)), 1))
  ++ (List.range k).map (fun t => ((.W (t + 1), .T1), 1))
  ++ (List.range k).map (fun t => ((.W (t + 1), .T2), 1))
  ++ (List.range k).map (fun t => ((.U (t + 1), .W (t + 1)), 1))
  ++ (List.range (k - 1)).map (fun t => ((.U (t + 2), .W (t + 1)), 1))

theorem oarcs_total (k : ℕ) (hk : 1 ≤ k) : ((oarcs k).map Prod.snd).sum = 6 * k + 14 := by
  simp only [oarcs, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil, List.map_map, Function.comp_def, sum_map_range_one]
  omega

/-- Every listed arc is an arc of `G_{2k+6}` between two of its vertices. -/
theorem oarcs_arcs (k : ℕ) (hk : 1 ≤ k) :
    ∀ q ∈ oarcs k, valid k q.1.1 ∧ valid k q.1.2 ∧ garc k q.1.1 q.1.2 := by
  intro q hq
  simp only [oarcs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hq
  rcases hq with ((((((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | ⟨t, ht, h⟩) |
    ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩ <;>
    (subst h; simp only [valid, garc, and_true, true_and, and_self]; try omega)

/-- The forward weight of Alice's arcs under the ranking `r`. -/
theorem oarcs_fwd (k : ℕ) (r : V → ℕ) :
    ((oarcs k).map (fun q => if r q.1.1 < r q.1.2 then q.2 else 0)).sum =
      fw r .T0 .T3 + fw r .T2 .P1 + fw r .T3 .P1 + fw r .P1 .T0 + fw r .P1 .T1 + fw r .T1 .P2
      + fw r .T3 .P2 + fw r .P2 .T0 + fw r .P2 .T2 + fw r .T0 .T1 + fw r .T0 .T2 + fw r .T1 .T3
      + fw r .T2 .T3 + fw r (.U 1) .T0 + fw r .T3 (.W k)
      + ∑ t ∈ Finset.range k, fw r .T1 (.U (t + 1)) + ∑ t ∈ Finset.range k, fw r .T2 (.U (t + 1))
      + ∑ t ∈ Finset.range k, fw r (.W (t + 1)) .T1 + ∑ t ∈ Finset.range k, fw r (.W (t + 1)) .T2
      + ∑ t ∈ Finset.range k, fw r (.U (t + 1)) (.W (t + 1))
      + ∑ t ∈ Finset.range (k - 1), fw r (.U (t + 2)) (.W (t + 1)) := by
  simp only [oarcs, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil, List.map_map, Function.comp_def, list_range_sum, fw]
  ring

/-- Alice's side: every ranking makes at most `4k + 9 = 2n - 3` arcs of `G_{2k+6}` forward. -/
theorem alice (k : ℕ) (hk : 1 ≤ k) : AliceFwd (oarcs k) (4 * k + 9) := by
  intro r
  rw [oarcs_fwd]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- the hub triangles of the arcs U_i → W_i
  have hdiag : ∑ t ∈ Finset.range (m + 1),
      (2 * fw r (.U (t + 1)) (.W (t + 1)) + fw r .T1 (.U (t + 1)) + fw r .T2 (.U (t + 1))
        + fw r (.W (t + 1)) .T1 + fw r (.W (t + 1)) .T2) ≤ ∑ t ∈ Finset.range (m + 1), 4 := by
    apply Finset.sum_le_sum
    intro t _
    have h1 := tri r (.U (t + 1)) (.W (t + 1)) .T1
    have h2 := tri r (.U (t + 1)) (.W (t + 1)) .T2
    omega
  -- the hub triangles of the arcs U_{i+1} → W_i
  have hoff : ∑ t ∈ Finset.range m,
      (2 * fw r (.U (t + 2)) (.W (t + 1)) + fw r .T1 (.U (t + 1 + 1)) + fw r .T2 (.U (t + 1 + 1))
        + fw r (.W (t + 1)) .T1 + fw r (.W (t + 1)) .T2) ≤ ∑ t ∈ Finset.range m, 4 := by
    apply Finset.sum_le_sum
    intro t _
    have h1 : fw r (.U (t + 2)) (.W (t + 1)) + fw r (.W (t + 1)) .T1 + fw r .T1 (.U (t + 1 + 1)) ≤ 2 :=
      tri r (.U (t + 2)) (.W (t + 1)) .T1
    have h2 : fw r (.U (t + 2)) (.W (t + 1)) + fw r (.W (t + 1)) .T2 + fw r .T2 (.U (t + 1 + 1)) ≤ 2 :=
      tri r (.U (t + 2)) (.W (t + 1)) .T2
    omega
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hdiag hoff
  -- index shifts: the sums over U start at U_1, those over W end at W_{m+1}
  have sU1 := Finset.sum_range_succ' (fun t => fw r .T1 (.U (t + 1))) m
  have sU2 := Finset.sum_range_succ' (fun t => fw r .T2 (.U (t + 1))) m
  have sW1 := Finset.sum_range_succ (fun t => fw r (.W (t + 1)) .T1) m
  have sW2 := Finset.sum_range_succ (fun t => fw r (.W (t + 1)) .T2) m
  simp only [Nat.zero_add] at sU1 sU2
  -- the ends of the path, the six triangles on fixed vertices and the defect 4-cycle
  have e1 := tri r (.U 1) .T0 .T1
  have e2 := tri r (.U 1) .T0 .T2
  have e3 := tri r .T3 (.W (m + 1)) .T1
  have e4 := tri r .T3 (.W (m + 1)) .T2
  have f1 := tri r .T0 .T3 .P1
  have f2 := tri r .T0 .T3 .P2
  have f3 := tri r .T2 .P1 .T0
  have f4 := tri r .T1 .P2 .T0
  have f5 := tri r .T3 .P1 .T1
  have f6 := tri r .T3 .P2 .T2
  have d := quad r .T1 .P2 .T2 .P1
  omega

end Tsigma.Even
