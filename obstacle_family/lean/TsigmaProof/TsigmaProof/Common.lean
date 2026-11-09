import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Shared definitions for the predictability of the completions of `G_n` and `H_n`

Paper 1, Section `sec:family` and Appendix `app:family`.  A *ranking* is a function `r : V → ℕ`;
it makes the arc `x → y` *forward* if `r x < r y` and *reverses* it if `r y < r x`.  A linear order
of a finite vertex set is a ranking that is injective on it.

The predictability `α*(D)` of a digraph `D` is the value of the game in which Alice picks an arc
and Bob a linear order, Bob winning when the arc is forward.  We state both sides with integer
weights, which is the same as the rational statement after dividing by the total weight:

* `BobFwd L E vs β`: the weighted rankings `L` make every arc of `E` between vertices of `vs`
  forward with total weight at least `β`;
* `AliceFwd A γ`: every ranking makes the arcs of the weighted list `A` forward with total weight
  at most `γ`.

`weak_duality` shows that if Bob's weights total `B` and Alice's total `C`, then `β * C ≤ γ * B`,
so `β / B ≤ γ / C`: when `β / B = γ / C` this common ratio is the value of the game.
-/

namespace Tsigma

variable {V : Type}

/-- `1` if the ranking `r` reverses the arc `x → y`, `0` otherwise. -/
def ind (r : V → ℕ) (x y : V) : ℕ := if r y < r x then 1 else 0

theorem ind_of_lt {r : V → ℕ} {x y : V} (h : r y < r x) : ind r x y = 1 := by
  simp [ind, h]

theorem ind_of_not_lt {r : V → ℕ} {x y : V} (h : ¬ r y < r x) : ind r x y = 0 := by
  simp [ind, h]

/-- Number of members `t < m` of a family of rankings that reverse `x → y`. -/
def famsum (f : ℕ → V → ℕ) (m : ℕ) (x y : V) : ℕ := ((List.range m).map (fun t => ind (f t) x y)).sum

theorem famsum_eq_card (f : ℕ → V → ℕ) (m : ℕ) (x y : V) :
    famsum f m x y = ((Finset.range m).filter (fun t => f t y < f t x)).card := by
  induction m with
  | zero => simp [famsum]
  | succ m ih =>
    simp only [famsum] at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : f m y < f m x
    · simp only [h, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      simp [ind, h]
    · simp only [h, ↓reduceIte]
      simp [ind, h]

/-- A family's count is an interval length when the members that reverse the arc form the
interval `[a, b)` of the index range `[0, m)`. -/
theorem famsum_interval {f : ℕ → V → ℕ} {m : ℕ} {x y : V} (a b : ℕ)
    (h : ∀ t, t < m → (f t y < f t x ↔ a ≤ t ∧ t < b)) (hb : a < b → b ≤ m) :
    famsum f m x y = b - a := by
  rw [famsum_eq_card]
  by_cases hab : a < b
  · have : (Finset.range m).filter (fun t => f t y < f t x) = Finset.Ico a b := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩; exact (h t h1).1 h2
      · rintro ⟨h1, h2⟩; have := hb hab; exact ⟨by omega, (h t (by omega)).2 ⟨h1, h2⟩⟩
    rw [this, Nat.card_Ico]
  · have : (Finset.range m).filter (fun t => f t y < f t x) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      intro h1 h2
      have := (h t h1).1 h2
      omega
    rw [this, Finset.card_empty]
    omega

theorem sum_map_range_one (m : ℕ) : ((List.range m).map (fun _ => (1 : ℕ))).sum = m := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp

/-- Total weight with which the weighted rankings `L` make `x → y` forward. -/
def fwdWeight (L : List (ℕ × (V → ℕ))) (x y : V) : ℕ :=
  (L.map (fun p => if p.2 x < p.2 y then p.1 else 0)).sum

/-- Total weight with which `L` reverses `x → y`. -/
def revWeight (L : List (ℕ × (V → ℕ))) (x y : V) : ℕ :=
  (L.map (fun p => p.1 * ind p.2 x y)).sum

/-- Bob's guarantee: every arc of `E` between vertices of `vs` is forward with weight `≥ β`. -/
def BobFwd (L : List (ℕ × (V → ℕ))) (E : V → V → Prop) (vs : List V) (β : ℕ) : Prop :=
  ∀ x ∈ vs, ∀ y ∈ vs, E x y → β ≤ fwdWeight L x y

/-- Alice's guarantee: every ranking makes the weighted arcs of `A` forward with weight `≤ γ`. -/
def AliceFwd (A : List ((V × V) × ℕ)) (γ : ℕ) : Prop :=
  ∀ r : V → ℕ, (A.map (fun q => if r q.1.1 < r q.1.2 then q.2 else 0)).sum ≤ γ

/-- For a ranking that is injective on `{x, y}`, forward and reverse weights add up to the total. -/
theorem fwd_add_rev (L : List (ℕ × (V → ℕ))) (x y : V) (hxy : ∀ p ∈ L, p.2 x ≠ p.2 y) :
    fwdWeight L x y + revWeight L x y = (L.map Prod.fst).sum := by
  induction L with
  | nil => simp [fwdWeight, revWeight]
  | cons p L ih =>
    have hp := hxy p (by simp)
    have ih' := ih (fun q hq => hxy q (by simp [hq]))
    simp only [fwdWeight, revWeight, List.map_cons, List.sum_cons] at ih' ⊢
    have key : (if p.2 x < p.2 y then p.1 else 0) + p.1 * ind p.2 x y = p.1 := by
      unfold ind
      rcases Nat.lt_or_gt_of_ne hp with h | h
      · simp [h, Nat.lt_asymm h]
      · simp [h, Nat.lt_asymm h]
    omega

/-- Total weight with which the ranking `r` makes the weighted arcs of `A` forward. -/
def aliceWeight (A : List ((V × V) × ℕ)) (r : V → ℕ) : ℕ :=
  (A.map (fun q => if r q.1.1 < r q.1.2 then q.2 else 0)).sum

/-- The double sum over Bob's rankings and Alice's arcs, taken in either order. -/
theorem double_count (L : List (ℕ × (V → ℕ))) (A : List ((V × V) × ℕ)) :
    (A.map (fun q => q.2 * fwdWeight L q.1.1 q.1.2)).sum =
      (L.map (fun p => p.1 * aliceWeight A p.2)).sum := by
  induction L with
  | nil => simp [fwdWeight]
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    have : ∀ q : (V × V) × ℕ, q.2 * fwdWeight (p :: L) q.1.1 q.1.2 =
        p.1 * (if p.2 q.1.1 < p.2 q.1.2 then q.2 else 0) + q.2 * fwdWeight L q.1.1 q.1.2 := by
      intro q
      simp only [fwdWeight, List.map_cons, List.sum_cons]
      split <;> ring
    simp only [this, List.sum_map_add, List.sum_map_mul_left, aliceWeight]

/-- Weak duality, in integer form: Bob's weights `L` (total `B`, every arc of `E` between vertices
of `vs` forward with weight `≥ β`) against Alice's weights `A` (total `C`, on such arcs, every
ranking forward with weight `≤ γ`) give `β * C ≤ γ * B`, that is `β / B ≤ γ / C`. -/
theorem weak_duality (L : List (ℕ × (V → ℕ))) (A : List ((V × V) × ℕ)) (E : V → V → Prop)
    (vs : List V) (β γ : ℕ) (hL : BobFwd L E vs β) (hA : AliceFwd A γ)
    (hAE : ∀ q ∈ A, q.1.1 ∈ vs ∧ q.1.2 ∈ vs ∧ E q.1.1 q.1.2) :
    β * (A.map Prod.snd).sum ≤ γ * (L.map Prod.fst).sum := by
  have h1 : β * (A.map Prod.snd).sum ≤ (A.map (fun q => q.2 * fwdWeight L q.1.1 q.1.2)).sum := by
    rw [mul_comm, ← List.sum_map_mul_right]
    apply List.sum_le_sum
    intro q hq
    obtain ⟨hx, hy, he⟩ := hAE q hq
    exact Nat.mul_le_mul_left _ (hL _ hx _ hy he)
  have h2 : (L.map (fun p => p.1 * aliceWeight A p.2)).sum ≤ γ * (L.map Prod.fst).sum := by
    rw [mul_comm, ← List.sum_map_mul_right]
    apply List.sum_le_sum
    intro p _
    exact Nat.mul_le_mul_left _ (hA p.2)
  rw [double_count] at h1
  exact le_trans h1 h2

end Tsigma
