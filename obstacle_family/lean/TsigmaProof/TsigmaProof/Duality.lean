import TsigmaProof.Common
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Optimal Alice strategies: support and tight orders (Lemmas `lem:family-loads`, `lem:family-moves`)

An *Alice strategy* is a function `y : V → V → ℚ`, nonnegative, with total `1` over the ordered pairs of
the vertex list `vs`, and zero outside the arcs of a digraph `E`.  It is *optimal with value `ρ`* when every
linear order of `vs` (a ranking injective on `vs`) makes the arcs forward with total weight at most `ρ`.

* `support_of_strict` (Lemma `lem:family-loads`): if Bob's weighted orders, of total `B` with `B ρ = β`,
  make every arc of `E` forward with weight at least `β`, and every arc of `E` outside `M` with weight at
  least `β + 1`, then every optimal Alice strategy vanishes outside `M`.
* `tight` (first half of Lemma `lem:family-moves`): if Bob's weighted orders make every arc of `M`
  forward with weight at least `β`, then every order of positive weight makes the arcs of an optimal
  Alice strategy supported on `M` forward with weight exactly `ρ`.
* `move_le` (second half of Lemma `lem:family-moves`): moving one vertex `u` of such an order to a new
  place (rank `q`, odd, against the doubled ranks of the others), so that exactly two arcs of `M` change
  direction, `g` becoming forward and `l` backward, gives `y g ≤ y l`.
-/

namespace Tsigma

open Finset

variable {V : Type} [DecidableEq V]

/-- The sum of `f` over the ordered pairs of vertices of `vs`. -/
def psum (vs : List V) (f : V → V → ℚ) : ℚ := ∑ x ∈ vs.toFinset, ∑ z ∈ vs.toFinset, f x z

/-- The total weight that the ranking `r` makes forward. -/
def fwdQ (vs : List V) (r : V → ℕ) (y : V → V → ℚ) : ℚ :=
  psum vs (fun x z => if r x < r z then y x z else 0)

/-- `r` is a linear order of `vs`: it is injective on `vs`. -/
def LinOrd (vs : List V) (r : V → ℕ) : Prop := ∀ x ∈ vs, ∀ z ∈ vs, x ≠ z → r x ≠ r z

/-- `y` is an optimal Alice strategy, supported on `E`, against the linear orders of `vs`, of value `ρ`. -/
structure AliceOpt (vs : List V) (E : V → V → Prop) (ρ : ℚ) (y : V → V → ℚ) : Prop where
  nonneg : ∀ x z, 0 ≤ y x z
  supp : ∀ x z, y x z ≠ 0 → E x z
  total : psum vs y = 1
  opt : ∀ r, LinOrd vs r → fwdQ vs r y ≤ ρ

theorem psum_congr {vs : List V} {f g : V → V → ℚ} (h : ∀ x ∈ vs, ∀ z ∈ vs, f x z = g x z) :
    psum vs f = psum vs g := by
  unfold psum
  refine Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun z hz => ?_))
  exact h x (List.mem_toFinset.1 hx) z (List.mem_toFinset.1 hz)

theorem psum_le {vs : List V} {f g : V → V → ℚ} (h : ∀ x ∈ vs, ∀ z ∈ vs, f x z ≤ g x z) :
    psum vs f ≤ psum vs g := by
  unfold psum
  refine Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun z hz => ?_))
  exact h x (List.mem_toFinset.1 hx) z (List.mem_toFinset.1 hz)

theorem psum_add (vs : List V) (f g : V → V → ℚ) :
    psum vs (fun x z => f x z + g x z) = psum vs f + psum vs g := by
  unfold psum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib)

theorem psum_sub (vs : List V) (f g : V → V → ℚ) :
    psum vs (fun x z => f x z - g x z) = psum vs f - psum vs g := by
  unfold psum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_sub_distrib _ _)

theorem psum_mul_left (vs : List V) (c : ℚ) (f : V → V → ℚ) :
    psum vs (fun x z => c * f x z) = c * psum vs f := by
  unfold psum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])

theorem le_psum {vs : List V} {f : V → V → ℚ} (h0 : ∀ x ∈ vs, ∀ z ∈ vs, 0 ≤ f x z) {a b : V}
    (ha : a ∈ vs) (hb : b ∈ vs) : f a b ≤ psum vs f := by
  unfold psum
  have hin : f a b ≤ ∑ z ∈ vs.toFinset, f a z :=
    Finset.single_le_sum (f := fun z => f a z) (fun z hz => h0 a ha z (List.mem_toFinset.1 hz))
      (List.mem_toFinset.2 hb)
  have hout : ∑ z ∈ vs.toFinset, f a z ≤ ∑ x ∈ vs.toFinset, ∑ z ∈ vs.toFinset, f x z :=
    Finset.single_le_sum (f := fun x => ∑ z ∈ vs.toFinset, f x z)
      (fun x hx => Finset.sum_nonneg (fun z hz => h0 x (List.mem_toFinset.1 hx) z
        (List.mem_toFinset.1 hz))) (List.mem_toFinset.2 ha)
  linarith

theorem psum_delta (vs : List V) {a b : V} (ha : a ∈ vs) (hb : b ∈ vs) (c : ℚ) :
    psum vs (fun x z => if (x, z) = (a, b) then c else 0) = c := by
  unfold psum
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro z _ hz
      simp [hz]
    · intro h
      exact absurd (List.mem_toFinset.2 hb) h
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro z _
    simp [hx]
  · intro h
    exact absurd (List.mem_toFinset.2 ha) h

/-- Double counting: Bob's orders weighted by Alice's forward weight, against Alice's arcs weighted by
their forward weight under Bob's orders. -/
theorem double_countQ (vs : List V) (L : List (ℕ × (V → ℕ))) (y : V → V → ℚ) :
    (L.map (fun p => (p.1 : ℚ) * fwdQ vs p.2 y)).sum =
      psum vs (fun x z => y x z * (fwdWeight L x z : ℚ)) := by
  induction L with
  | nil => simp [fwdWeight, psum]
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have key : ∀ x z, y x z * (fwdWeight (p :: L) x z : ℚ) =
        (p.1 : ℚ) * (if p.2 x < p.2 z then y x z else 0) + y x z * (fwdWeight L x z : ℚ) := by
      intro x z
      simp only [fwdWeight, List.map_cons, List.sum_cons]
      push_cast
      split_ifs <;> ring
    rw [psum_congr (fun x _ z _ => key x z), psum_add, psum_mul_left]
    rfl

theorem weighted_le (vs : List V) (L : List (ℕ × (V → ℕ))) (y : V → V → ℚ) (ρ : ℚ)
    (h : ∀ p ∈ L, fwdQ vs p.2 y ≤ ρ) :
    (L.map (fun p => (p.1 : ℚ) * fwdQ vs p.2 y)).sum ≤ ((L.map Prod.fst).sum : ℚ) * ρ := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    have h1 := h p (by simp)
    have h2 := ih (fun q hq => h q (by simp [hq]))
    have h3 : (p.1 : ℚ) * fwdQ vs p.2 y ≤ p.1 * ρ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [add_mul]
    linarith

theorem gap_sum (vs : List V) (L : List (ℕ × (V → ℕ))) (y : V → V → ℚ) (ρ : ℚ) :
    (L.map (fun p => (p.1 : ℚ) * (ρ - fwdQ vs p.2 y))).sum =
      ((L.map Prod.fst).sum : ℚ) * ρ - (L.map (fun p => (p.1 : ℚ) * fwdQ vs p.2 y)).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    ring

/-- **Lemma `lem:family-loads`**, support half: a strict certificate confines every optimal Alice
strategy to `M`. -/
theorem support_of_strict (vs : List V) (L : List (ℕ × (V → ℕ))) (B β : ℕ) (ρ : ℚ)
    (hB : (L.map Prod.fst).sum = B) (hρ : (B : ℚ) * ρ = β) (hinj : ∀ p ∈ L, LinOrd vs p.2)
    (E M : V → V → Prop) (hfw : ∀ x ∈ vs, ∀ z ∈ vs, E x z → β ≤ fwdWeight L x z)
    (hstr : ∀ x ∈ vs, ∀ z ∈ vs, E x z → ¬ M x z → β + 1 ≤ fwdWeight L x z)
    (y : V → V → ℚ) (hy : AliceOpt vs E ρ y) : ∀ x ∈ vs, ∀ z ∈ vs, ¬ M x z → y x z = 0 := by
  have hle := weighted_le vs L y ρ (fun p hp => hy.opt p.2 (hinj p hp))
  rw [hB, hρ, double_countQ] at hle
  have hg0 : ∀ x ∈ vs, ∀ z ∈ vs, 0 ≤ y x z * ((fwdWeight L x z : ℚ) - β) := by
    intro x hx z hz
    by_cases h0 : y x z = 0
    · simp [h0]
    · have h1 : (β : ℚ) ≤ fwdWeight L x z := by exact_mod_cast hfw x hx z hz (hy.supp x z h0)
      exact mul_nonneg (hy.nonneg x z) (by linarith)
  have hsum : psum vs (fun x z => y x z * ((fwdWeight L x z : ℚ) - β)) =
      psum vs (fun x z => y x z * (fwdWeight L x z : ℚ)) - β := by
    have : psum vs (fun x z => y x z * ((fwdWeight L x z : ℚ) - β)) =
        psum vs (fun x z => y x z * (fwdWeight L x z : ℚ)) - (β : ℚ) * psum vs y := by
      rw [← psum_mul_left, ← psum_sub]
      exact psum_congr (fun x _ z _ => by ring)
    rw [this, hy.total, mul_one]
  intro x hx z hz hM
  have hterm := le_psum hg0 hx hz
  rw [hsum] at hterm
  by_contra h0
  have h1 : (β : ℚ) + 1 ≤ fwdWeight L x z := by
    exact_mod_cast hstr x hx z hz (hy.supp x z h0) hM
  have hpos : 0 < y x z := lt_of_le_of_ne (hy.nonneg x z) (Ne.symm h0)
  have h2 : y x z * 1 ≤ y x z * ((fwdWeight L x z : ℚ) - β) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  linarith

/-- **Lemma `lem:family-moves`**, first half: every order of positive weight in an optimal Bob strategy
for `M` is tight for every optimal Alice strategy supported on `M`. -/
theorem tight (vs : List V) (L : List (ℕ × (V → ℕ))) (B β : ℕ) (ρ : ℚ)
    (hB : (L.map Prod.fst).sum = B) (hρ : (B : ℚ) * ρ = β) (hinj : ∀ p ∈ L, LinOrd vs p.2)
    (M : V → V → Prop) (hfw : ∀ x ∈ vs, ∀ z ∈ vs, M x z → β ≤ fwdWeight L x z)
    (y : V → V → ℚ) (hy : AliceOpt vs M ρ y) : ∀ p ∈ L, 0 < p.1 → fwdQ vs p.2 y = ρ := by
  have hge : (β : ℚ) ≤ psum vs (fun x z => y x z * (fwdWeight L x z : ℚ)) := by
    have h1 : psum vs (fun x z => (β : ℚ) * y x z) ≤
        psum vs (fun x z => y x z * (fwdWeight L x z : ℚ)) := by
      refine psum_le (fun x hx z hz => ?_)
      by_cases h0 : y x z = 0
      · simp [h0]
      · have : (β : ℚ) ≤ fwdWeight L x z := by exact_mod_cast hfw x hx z hz (hy.supp x z h0)
        nlinarith [hy.nonneg x z]
    rw [psum_mul_left, hy.total, mul_one] at h1
    exact h1
  have hgap := gap_sum vs L y ρ
  rw [hB, hρ, double_countQ] at hgap
  have hnn : ∀ q ∈ L.map (fun p => (p.1 : ℚ) * (ρ - fwdQ vs p.2 y)), 0 ≤ q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact mul_nonneg (by positivity) (by linarith [hy.opt p.2 (hinj p hp)])
  intro p hp hpos
  have hle := List.single_le_sum hnn _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  rw [hgap] at hle
  have hopt := hy.opt p.2 (hinj p hp)
  have hp1 : (0 : ℚ) < p.1 := by exact_mod_cast hpos
  have : (p.1 : ℚ) * (ρ - fwdQ vs p.2 y) ≤ 0 := by linarith
  have : ρ - fwdQ vs p.2 y ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hp1 hc
    linarith
  linarith

/-- The ranking `π` with `u` moved to the odd rank `q`, against the ranks `2 π v + 2` of the others:
`q = 2 π t + 1` puts `u` just before `t`, and `q = 2 π t + 3` just after `t`. -/
def moved (π : V → ℕ) (u : V) (q : ℕ) (v : V) : ℕ := if v = u then q else 2 * π v + 2

theorem moved_lin (vs : List V) (π : V → ℕ) (hπ : LinOrd vs π) (u : V) (q : ℕ) (hq : q % 2 = 1) :
    LinOrd vs (moved π u q) := by
  intro x hx z hz hxz
  unfold moved
  by_cases h1 : x = u <;> by_cases h2 : z = u
  · exact absurd (h1.trans h2.symm) hxz
  · simp only [h1, h2, if_true, if_false]; omega
  · simp only [h1, h2, if_true, if_false]; omega
  · simp only [h1, h2, if_false]
    have := hπ x hx z hz hxz
    omega

/-- **Lemma `lem:family-moves`**, second half: a move that changes exactly two arcs of `M`. -/
theorem move_le (vs : List V) (M : V → V → Prop) (ρ : ℚ) (y : V → V → ℚ) (hy : AliceOpt vs M ρ y)
    (π : V → ℕ) (hπ : LinOrd vs π) (ht : fwdQ vs π y = ρ) (u : V) (q : ℕ) (hq : q % 2 = 1)
    (g1 g2 l1 l2 : V) (hg1 : g1 ∈ vs) (hg2 : g2 ∈ vs) (hl1 : l1 ∈ vs) (hl2 : l2 ∈ vs)
    (hgl : (g1, g2) ≠ (l1, l2))
    (hgf : moved π u q g1 < moved π u q g2) (hgb : ¬ π g1 < π g2)
    (hlf : ¬ moved π u q l1 < moved π u q l2) (hlb : π l1 < π l2)
    (hoth : ∀ v ∈ vs, v ≠ u →
      (M u v → (u, v) ≠ (g1, g2) → (u, v) ≠ (l1, l2) → (q < 2 * π v + 2 ↔ π u < π v)) ∧
      (M v u → (v, u) ≠ (g1, g2) → (v, u) ≠ (l1, l2) → (2 * π v + 2 < q ↔ π v < π u))) :
    y g1 g2 ≤ y l1 l2 := by
  have hpt : ∀ x ∈ vs, ∀ z ∈ vs,
      (if moved π u q x < moved π u q z then y x z else 0) =
        ((if π x < π z then y x z else 0) + (if (x, z) = (g1, g2) then y g1 g2 else 0)) -
          (if (x, z) = (l1, l2) then y l1 l2 else 0) := by
    intro x hx z hz
    by_cases hxg : (x, z) = (g1, g2)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxg
      rw [if_pos hgf, if_neg hgb, if_pos rfl, if_neg hgl]
      ring
    by_cases hxl : (x, z) = (l1, l2)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxl
      rw [if_neg hlf, if_pos hlb, if_neg hxg, if_pos rfl]
      ring
    simp only [hxg, hxl, if_false, add_zero, sub_zero]
    by_cases hy0 : y x z = 0
    · simp [hy0]
    have hM := hy.supp x z hy0
    have hiff : moved π u q x < moved π u q z ↔ π x < π z := by
      unfold moved
      by_cases h1 : x = u <;> by_cases h2 : z = u
      · subst h1; subst h2; simp
      · subst h1
        simp only [if_true, h2, if_false]
        exact (hoth z hz h2).1 hM hxg hxl
      · subst h2
        simp only [h1, if_false, if_true]
        exact (hoth x hx h1).2 hM hxg hxl
      · simp only [h1, h2, if_false]
        omega
    simp only [hiff]
  have hmv := hy.opt _ (moved_lin vs π hπ u q hq)
  have heq : fwdQ vs (moved π u q) y = fwdQ vs π y + y g1 g2 - y l1 l2 := by
    unfold fwdQ
    rw [psum_congr hpt, psum_sub, psum_add, psum_delta vs hg1 hg2, psum_delta vs hl1 hl2]
  linarith

/-- Sums over the ordered pairs of `vs` of a function supported on the pairs listed in `P` (each once)
are sums over `P`. -/
theorem psum_eq_list (vs : List V) (P : List (V × V)) (hP : P.Nodup)
    (hPvs : ∀ q ∈ P, q.1 ∈ vs ∧ q.2 ∈ vs) (f : V → V → ℚ)
    (hf : ∀ x ∈ vs, ∀ z ∈ vs, f x z ≠ 0 → (x, z) ∈ P) :
    psum vs f = (P.map (fun q => f q.1 q.2)).sum := by
  unfold psum
  rw [← Finset.sum_product' (f := f), ← List.sum_toFinset _ hP]
  symm
  apply Finset.sum_subset
  · intro q hq
    have := hPvs q (List.mem_toFinset.1 hq)
    exact Finset.mem_product.2 ⟨List.mem_toFinset.2 this.1, List.mem_toFinset.2 this.2⟩
  · intro q hq hqP
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    by_contra hne
    exact hqP (List.mem_toFinset.2 (hf q.1 (List.mem_toFinset.1 h1) q.2 (List.mem_toFinset.1 h2) hne))

end Tsigma
